import type { Diagram, NodeId, RegionId } from '../../kernel/diagram/diagram'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import {
  beginBodyPlacement,
  cancelBodyPlacement,
  previewBodyPlacement,
  type BodyPlacement,
} from '../../view/placement'
import type { Vec2 } from '../../view/vec'
import {
  absorbHits,
  addRelationWire,
  addCut,
  deleteHits,
  joinWires,
  reparentNode,
  severEndpoint,
} from '../edit'
import { relSig, IOTA } from '../../kernel/diagram/sig'
import { buildSelection, type Hit } from '../hittest'
import { ConnectionDragController } from './connection'
import { CopyDragController } from './copy'
import { copyDestinationPreview, copySelectionPreview } from './copy-view'
import { applyIdentitySteps, IdentityOpsController } from './identity-ops'
import { SlashController } from './slash'
import type { KeySample, PointerClaim, PointerSample } from './viewport'
import type { CopyDestination, CopyPlan } from '../copy-planner'

type PlacementState = { readonly node: NodeId; readonly placement: BodyPlacement; at: Vec2 }

type Preview = { readonly kind: 'placement'; readonly state: PlacementState }

export type ConstructOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly diagram: () => Diagram
  readonly selection: () => readonly Hit[]
  readonly setSelection: (selection: readonly Hit[]) => void
  readonly commit: (diagram: Diagram) => void
  readonly refuse: (text: string, pointer?: Vec2) => void
  readonly setProblem: (problemId: string, text: string) => void
  readonly clearProblem: (problemId: string) => void
  readonly openSpawn: (sample: PointerSample, region: RegionId) => void
  readonly theme: () => Theme
  readonly copy?: {
    readonly destination: (sample: PointerSample) => CopyDestination | null
    readonly commit: (plan: CopyPlan, sample: PointerSample) => void
  }
}

function sameHit(a: Hit, b: Hit): boolean {
  return a.kind === b.kind && a.id === b.id
}

function regionAt(engine: Engine, diagram: Diagram, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, region] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (Math.hypot(point.x - region.center.x, point.y - region.center.y) <= region.radius
      && (best === null || region.radius < best.radius)) best = { id, radius: region.radius }
  }
  return best?.id ?? diagram.root
}

export class ConstructController {
  readonly #options: ConstructOptions
  readonly #identity: IdentityOpsController
  readonly #connection: ConnectionDragController
  readonly #copy: CopyDragController | null
  readonly #slash: SlashController
  #preview: Preview | null = null
  #prompt: HTMLDivElement | null = null

  constructor(options: ConstructOptions) {
    this.#options = options
    this.#identity = new IdentityOpsController({
      active: options.active,
      engine: options.engine,
      diagram: options.diagram,
      viewScale: options.viewScale,
      theme: options.theme,
      claimEndDiscs: true,
      commit: (label, steps) => this.#tryCommit(
        () => applyIdentitySteps(this.#options.diagram(), steps), label,
      ),
      refuse: options.refuse,
    })
    this.#slash = new SlashController({
      active: options.active,
      engine: options.engine,
      diagram: options.diagram,
      theme: options.theme,
      still: (sample) => {
        this.#options.openSpawn(sample, regionAt(this.#options.engine(), this.#options.diagram(), sample.world))
      },
      commit: (crossings, sample) => {
        let next = this.#options.diagram()
        let severed = 0
        for (const crossing of crossings) {
          try {
            next = severEndpoint(next, crossing.wire, crossing.endpoint)
            severed++
          } catch (error) {
            this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
          }
        }
        if (severed > 0) this.#options.commit(next)
      },
      refuse: options.refuse,
    })
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: (gesture, pointer) => {
        const { source, target } = gesture
        if (source.wire === target.wire) {
          this.#options.refuse('release on another line to join', pointer)
          return false
        }
        return this.#tryCommit(() => joinWires(this.#options.diagram(), [source.wire, target.wire]), 'lines joined — one individual now')
      },
      refuse: options.refuse,
    })
    this.#copy = options.copy === undefined ? null : new CopyDragController({
      active: options.active,
      sourceDiagram: options.diagram,
      sourceSelection: options.selection,
      sourceEngine: options.engine,
      viewScale: options.viewScale,
      destination: options.copy.destination,
      commit: options.copy.commit,
      refuse: (text, sample) => options.refuse(text, sample.client),
      theme: options.theme,
      sourcePreview: copySelectionPreview,
      destinationPreview: (destination) => copyDestinationPreview(
        options.engine(), destination.region, options.theme(),
      ),
    })
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active()) return null
    if (sample.button === 2) return this.#slash.claim(sample)
    if (sample.button !== 0) return null

    const identity = this.#identity.claim(sample)
    if (identity !== null) return identity
    const connection = this.#connection.claim(sample)
    if (connection !== null) return connection
    const selected = this.#options.selection()
    const copy = this.#copy?.claim(sample) ?? null
    if (copy !== null) return copy

    if (sample.hit?.kind === 'node' && selected.some((hit) => sameHit(hit, sample.hit!))) {
      return this.#placementClaim(sample.hit.id)
    }
    return null
  }

  keyDown(sample: KeySample): boolean {
    if (!this.#options.active() || sample.repeat) return false
    if (sample.key === 'w' || sample.key === 'W') {
      const selected = absorbHits(this.#options.diagram(), this.#options.selection())
      if (selected.length === 0) {
        this.#options.refuse('select what the cut should go around first')
        return true
      }
      if (sample.shiftKey) this.#openRelationArityPrompt(selected)
      else this.#tryCommit(() => addCut(this.#options.diagram(), buildSelection(this.#options.diagram(), selected)).diagram, 'cut drawn around the selection')
      return true
    }
    if (sample.key === 'j' || sample.key === 'J') {
      const wires = this.#options.selection().filter((hit): hit is Extract<Hit, { kind: 'wire' }> => hit.kind === 'wire').map((hit) => hit.id)
      this.#tryCommit(() => joinWires(this.#options.diagram(), wires), `joined ${wires.length} lines — one individual now`)
      return true
    }
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      const selected = this.#options.selection()
      if (selected.length === 0) this.#options.refuse('nothing selected to delete')
      else this.#tryCommit(() => deleteHits(this.#options.diagram(), selected), 'deleted; selected boundaries dissolved and unselected contents propagated')
      return true
    }
    if (sample.key === 'Escape') {
      this.#identity.cancel()
      this.#copy?.cancel()
      if (this.#prompt !== null) {
        this.#closePrompt()
        return true
      }
      return false
    }
    return false
  }

  overlay(): readonly Shape[] {
    const connection = [
      ...this.#identity.overlay(),
      ...this.#connection.overlay(),
      ...(this.#copy?.overlay() ?? []),
      ...this.#slash.overlay(),
    ]
    const preview = this.#preview
    if (preview === null) return connection
    const colors = this.#options.theme().interaction
    const destination = regionAt(this.#options.engine(), this.#options.diagram(), preview.state.at)
    const home = this.#options.diagram().nodes[preview.state.node]?.region
    const geometry = this.#options.engine().regions.get(destination)
    return geometry === undefined || destination === home || this.#options.diagram().regions[destination]?.kind === 'sheet'
      ? connection
      : [...connection, { kind: 'circle', center: geometry.center, r: geometry.radius, fill: colors.validWash, stroke: colors.valid, width: 1.6, insetColor: null, glow: null }]
  }

  dispose(): void {
    this.#closePrompt()
    this.#identity.cancel()
    this.#connection.cancel()
    this.#copy?.dispose()
  }

  modifiersChanged(ctrlHeld: boolean): void { this.#copy?.modifiersChanged(ctrlHeld) }

  #placementClaim(node: NodeId): PointerClaim {
    const state: PlacementState = {
      node,
      placement: beginBodyPlacement(this.#options.engine(), node),
      at: { ...this.#options.engine().bodies.get(node)!.pos },
    }
    this.#preview = { kind: 'placement', state }
    return {
      still: 'selection',
      blocksPassiveRelaxation: false,
      relaxationPins: () => [node],
      move: (sample) => {
        state.at = sample.world
        previewBodyPlacement(this.#options.engine(), state.placement, sample.world)
      },
      release: (_sample, moved) => {
        this.#preview = null
        if (!moved) {
          cancelBodyPlacement(this.#options.engine(), state.placement)
          return
        }
        const destination = regionAt(this.#options.engine(), this.#options.diagram(), state.at)
        const home = this.#options.diagram().nodes[node]?.region
        if (home === destination) return
        if (!this.#tryCommit(() => reparentNode(this.#options.diagram(), node, destination), `moved into '${destination}'`)) {
          cancelBodyPlacement(this.#options.engine(), state.placement)
        }
      },
      cancel: () => {
        this.#preview = null
        cancelBodyPlacement(this.#options.engine(), state.placement)
      },
    }
  }

  #tryCommit(make: () => Diagram, _success: string): boolean {
    try {
      this.#options.commit(make())
      this.#options.setSelection([])
      return true
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error))
      return false
    }
  }

  #openRelationArityPrompt(selected: readonly Hit[]): void {
    this.#closePrompt()
    const prompt = this.#options.host.ownerDocument.createElement('div')
    prompt.className = 'vpa-relation-prompt'
    const input = this.#options.host.ownerDocument.createElement('input')
    input.className = 'vpa-relation-arity'
    input.type = 'number'
    input.min = '0'
    input.step = '1'
    input.placeholder = 'relation arity'
    input.setAttribute('aria-label', 'Relation arity')
    const theme = this.#options.theme()
    prompt.style.cssText = 'position:fixed;left:50%;top:56px;z-index:31;transform:translateX(-50%);display:grid;gap:4px'
    const problem = this.#options.host.ownerDocument.createElement('output')
    problem.id = 'relation-arity-problem'
    problem.className = 'vpa-field-problem'
    problem.style.setProperty('--vpa-field-problem', theme.interaction.refusal)
    problem.hidden = true
    prompt.append(input, problem)
    input.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') this.#closePrompt()
      if (event.key !== 'Enter') return
      const arity = Number(input.value)
      if (!Number.isInteger(arity) || arity < 0) {
        const text = `'${input.value}' is not a valid arity`
        this.#options.setProblem('relation-arity', text)
        problem.value = text
        problem.hidden = false
        input.setAttribute('aria-invalid', 'true')
        input.setAttribute('aria-describedby', problem.id)
        return
      }
      if (this.#tryCommit(
        () => addRelationWire(
          this.#options.diagram(),
          buildSelection(this.#options.diagram(), selected).region,
          relSig(Array.from({ length: arity }, () => IOTA)),
        ).diagram,
        'added a relation wire',
      )) this.#closePrompt()
    })
    input.addEventListener('input', () => {
      const value = Number(input.value)
      if (Number.isInteger(value) && value >= 0) {
        this.#options.clearProblem('relation-arity')
        problem.hidden = true
        problem.value = ''
        input.removeAttribute('aria-invalid')
        input.removeAttribute('aria-describedby')
      }
    })
    input.addEventListener('blur', () => this.#closePrompt())
    this.#prompt = prompt
    this.#options.host.append(prompt)
    queueMicrotask(() => input.focus())
  }

  #closePrompt(): void {
    this.#options.clearProblem('relation-arity')
    this.#prompt?.remove()
    this.#prompt = null
  }

}
