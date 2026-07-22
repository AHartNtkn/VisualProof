import type { Diagram, Endpoint, NodeId, RegionId } from '../kernel/diagram/diagram'
import { pkey, type Engine, type Leg } from '../view/engine'
import type { Shape, Theme } from '../view/paint'
import {
  beginBodyPlacement,
  cancelBodyPlacement,
  previewBodyPlacement,
  type BodyPlacement,
} from '../view/placement'
import type { Vec2 } from '../view/vec'
import { computeLegs, type LegGeom } from '../view/wires'
import {
  absorbHits,
  addBubble,
  addCut,
  deleteHits,
  joinWires,
  reparentNode,
  severEndpoint,
} from './edit'
import { buildSelection, type Hit } from './hittest'
import { ConnectionDragController } from './controllers/connection'
import { FissionDragController, type FissionRequest } from './controllers/fission'
import { CopyDragController, copyDestinationPreview } from './controllers/copy'
import type { KeySample, PointerClaim, PointerSample } from './controllers/viewport'
import type { CopyDestination, CopyPlan } from './copy-planner'

type PlacementState = { readonly node: NodeId; readonly placement: BodyPlacement; at: Vec2 }

type Preview =
  | { readonly kind: 'slash'; readonly from: Vec2; at: Vec2 }
  | { readonly kind: 'placement'; readonly state: PlacementState }

export type ConstructOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly diagram: () => Diagram
  readonly selection: () => readonly Hit[]
  readonly setSelection: (selection: readonly Hit[]) => void
  readonly commit: (diagram: Diagram) => void
  readonly commitFission: (request: FissionRequest) => void
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

function crosses(a: Vec2, b: Vec2, c: Vec2, d: Vec2): boolean {
  const orient = (p: Vec2, q: Vec2, r: Vec2): number => (q.x - p.x) * (r.y - p.y) - (q.y - p.y) * (r.x - p.x)
  const abC = orient(a, b, c)
  const abD = orient(a, b, d)
  const cdA = orient(c, d, a)
  const cdB = orient(c, d, b)
  const overlaps = (a0: number, a1: number, b0: number, b1: number): boolean =>
    Math.max(Math.min(a0, a1), Math.min(b0, b1)) <= Math.min(Math.max(a0, a1), Math.max(b0, b1))
  return abC * abD <= 0 && cdA * cdB <= 0
    && overlaps(a.x, b.x, c.x, d.x)
    && overlaps(a.y, b.y, c.y, d.y)
}

function crossedLegs(engine: Engine, from: Vec2, to: Vec2): LegGeom[] {
  return computeLegs(engine).filter((geometry) => {
    for (let i = 1; i < geometry.pts.length; i++) {
      if (crosses(from, to, geometry.pts[i - 1]!, geometry.pts[i]!)) return true
    }
    return false
  })
}

function endpointAt(diagram: Diagram, leg: Leg): Endpoint | null {
  for (const end of [leg.to, leg.from]) {
    if (diagram.nodes[end.body] === undefined) continue
    const endpoint = diagram.wires[leg.wid]?.endpoints.find((candidate) =>
      candidate.node === end.body && pkey(candidate.port) === end.key)
    if (endpoint !== undefined) return endpoint
  }
  return null
}

export class ConstructController {
  readonly #options: ConstructOptions
  readonly #connection: ConnectionDragController
  readonly #fission: FissionDragController
  readonly #copy: CopyDragController | null
  #preview: Preview | null = null
  #prompt: HTMLDivElement | null = null

  constructor(options: ConstructOptions) {
    this.#options = options
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: (source, target, pointer) => {
        if (source.wire === target.wire) {
          this.#options.refuse('release on another line to join', pointer)
          return false
        }
        return this.#tryCommit(() => joinWires(this.#options.diagram(), [source.wire, target.wire]), 'lines joined — one individual now')
      },
      refuse: options.refuse,
    })
    this.#fission = new FissionDragController({
      active: options.active,
      diagram: options.diagram,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: options.commitFission,
      refuse: (text, pointer) => options.refuse(text, pointer),
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
      destinationPreview: (destination) => copyDestinationPreview(
        options.engine(), destination.region, options.theme(),
      ),
    })
  }

  claim(sample: PointerSample): PointerClaim | null {
    if (!this.#options.active()) return null
    if (sample.button === 2) return this.#slashClaim(sample)
    if (sample.button !== 0) return null

    const connection = this.#connection.claim(sample)
    if (connection !== null) return connection
    const fission = this.#fission.claim(sample)
    if (fission !== null) return fission
    const selected = this.#options.selection()
    const copy = this.#copy?.claim(sample) ?? null
    if (copy !== null) { this.#fission.hover(null); return copy }

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
      if (sample.shiftKey) this.#openBubblePrompt(selected)
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
      const cancelledFission = this.#fission.cancel()
      this.#copy?.cancel()
      if (this.#prompt !== null) {
        this.#closePrompt()
        return true
      }
      return cancelledFission
    }
    return false
  }

  overlay(): readonly Shape[] {
    const connection = [...this.#connection.overlay(), ...this.#fission.overlay(), ...(this.#copy?.overlay() ?? [])]
    const preview = this.#preview
    if (preview === null) return connection
    const colors = this.#options.theme().interaction
    if (preview.kind === 'slash') {
      return [...connection, { kind: 'segment', from: preview.from, to: preview.at, stroke: colors.refusal, width: 2, glow: null }]
    }
    const destination = regionAt(this.#options.engine(), this.#options.diagram(), preview.state.at)
    const home = this.#options.diagram().nodes[preview.state.node]?.region
    const geometry = this.#options.engine().regions.get(destination)
    return geometry === undefined || destination === home || this.#options.diagram().regions[destination]?.kind === 'sheet'
      ? connection
      : [...connection, { kind: 'circle', center: geometry.center, r: geometry.radius, fill: colors.validWash, stroke: colors.valid, width: 1.6, insetColor: null, glow: null }]
  }

  dispose(): void {
    this.#closePrompt()
    this.#connection.cancel()
    this.#fission.dispose()
    this.#copy?.dispose()
  }

  passiveSample(sample: PointerSample | null): void { this.#fission.hover(this.#copy?.dragging === true ? null : sample) }
  modifiersChanged(ctrlHeld: boolean): void { this.#fission.modifiersChanged(ctrlHeld); this.#copy?.modifiersChanged(ctrlHeld) }

  #slashClaim(start: PointerSample): PointerClaim {
    const preview: Extract<Preview, { kind: 'slash' }> = { kind: 'slash', from: start.world, at: start.world }
    this.#preview = preview
    return {
      still: 'claim',
      blocksPassiveRelaxation: true,
      move: (sample) => { preview.at = sample.world },
      release: (sample, moved) => {
        this.#preview = null
        if (!moved) {
          this.#options.openSpawn(start, regionAt(this.#options.engine(), this.#options.diagram(), start.world))
          return
        }
        const crossings = crossedLegs(this.#options.engine(), preview.from, sample.world)
        if (crossings.length === 0) {
          this.#options.refuse('the slash crossed no strand', sample.client)
          return
        }
        let next = this.#options.diagram()
        let severed = 0
        let junctionOnly = false
        for (const crossing of crossings) {
          const endpoint = endpointAt(next, crossing.leg)
          if (endpoint === null) { junctionOnly = true; continue }
          try {
            next = severEndpoint(next, crossing.leg.wid, endpoint)
            severed++
          } catch (error) {
            this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
          }
        }
        if (severed > 0) {
          this.#options.commit(next)
        } else if (junctionOnly) this.#options.refuse('that strand runs between junctions; sever nearer a port', sample.client)
      },
      cancel: () => { this.#preview = null },
    }
  }

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

  #openBubblePrompt(selected: readonly Hit[]): void {
    this.#closePrompt()
    const prompt = this.#options.host.ownerDocument.createElement('div')
    prompt.className = 'vpa-bubble-prompt'
    const input = this.#options.host.ownerDocument.createElement('input')
    input.className = 'vpa-bubble-arity'
    input.type = 'number'
    input.min = '0'
    input.step = '1'
    input.placeholder = 'bubble arity'
    input.setAttribute('aria-label', 'Bubble arity')
    const theme = this.#options.theme()
    prompt.style.cssText = 'position:fixed;left:50%;top:56px;z-index:31;transform:translateX(-50%);display:grid;gap:4px'
    input.style.cssText = `width:9rem;padding:5px 8px;border:1.5px solid ${theme.interaction.selection};border-radius:6px;background:${theme.paper};color:${theme.ink}`
    const problem = this.#options.host.ownerDocument.createElement('output')
    problem.id = 'bubble-arity-problem'
    problem.className = 'vpa-field-problem'
    problem.style.cssText = `max-width:14rem;color:${theme.interaction.refusal};font:11px system-ui`
    problem.hidden = true
    prompt.append(input, problem)
    input.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') this.#closePrompt()
      if (event.key !== 'Enter') return
      const arity = Number(input.value)
      if (!Number.isInteger(arity) || arity < 0) {
        const text = `'${input.value}' is not a valid arity`
        this.#options.setProblem('bubble-arity', text)
        problem.value = text
        problem.hidden = false
        input.setAttribute('aria-invalid', 'true')
        input.setAttribute('aria-describedby', problem.id)
        return
      }
      if (this.#tryCommit(
        () => addBubble(this.#options.diagram(), buildSelection(this.#options.diagram(), selected), arity).diagram,
        'wrapped in a bubble',
      )) this.#closePrompt()
    })
    input.addEventListener('input', () => {
      const value = Number(input.value)
      if (Number.isInteger(value) && value >= 0) {
        this.#options.clearProblem('bubble-arity')
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
    this.#options.clearProblem('bubble-arity')
    this.#prompt?.remove()
    this.#prompt = null
  }

}
