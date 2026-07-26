import type { DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import { singleStepAction, type ProofAction } from '../../kernel/proof/action'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import type { ProofContext } from '../../kernel/proof/context'
import { EMPTY_PROOF_CONTEXT, assertProofContext } from '../../kernel/proof/context'
import { findDeiterationEvidence } from '../../kernel/rules/iteration'
import type {
  ContentOccurrence,
  WireJoinInput,
  WireSeverInput,
} from '../../kernel/rules/wire-quantifier'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import {
  applicableActions,
  type ActionDescriptor,
} from '../actions'
import { inferFoldArgs } from '../define'
import { absorbHits, orphanedWires } from '../edit'
import { buildSelection, type Hit } from '../hittest'
import { citationCandidates, citationStep, type CitationCandidate } from './cite'
import { ConnectionDragController, type ConnectionEnd } from './connection'
import { CopyDragController } from './copy'
import { copyDestinationPreview, copySelectionPreview } from './copy-view'
import type { KeySample, PointerClaim, PointerSample } from './viewport'

export type ProofOrientation = 'forward' | 'backward'

export type ProofDiscovery = {
  readonly sel: SubgraphSelection
  readonly actions: readonly ActionDescriptor[]
}

export function discoverProofActions(
  diagram: Diagram,
  hits: readonly Hit[],
  context: ProofContext,
  orientation: ProofOrientation,
): ProofDiscovery | null {
  assertProofContext(context)
  if (hits.length === 0) return null
  try {
    const sel = buildSelection(diagram, absorbHits(diagram, hits))
    return {
      sel,
      actions: applicableActions(diagram, sel, context, orientation === 'backward'),
    }
  } catch {
    return null
  }
}

function erasureSelection(diagram: Diagram, selection: SubgraphSelection): SubgraphSelection {
  const existing = new Set(selection.wires)
  const riders = orphanedWires(diagram, new Set(selection.nodes))
    .filter((wire) => !existing.has(wire) && diagram.wires[wire]!.scope === selection.region)
  return riders.length === 0
    ? selection
    : { ...selection, wires: [...selection.wires, ...riders] }
}

export function erasureStep(diagram: Diagram, selection: SubgraphSelection): ProofStep {
  return { rule: 'erasure', sel: erasureSelection(diagram, selection) }
}

export function deiterationStep(
  diagram: Diagram,
  selection: SubgraphSelection,
  fuel: number,
): ProofStep {
  const evidence = findDeiterationEvidence(diagram, selection, fuel)
  return {
    rule: 'deiteration',
    sel: selection,
    ...evidence,
    retargets: [],
  }
}

export function contextualDeleteStep(
  diagram: Diagram,
  discovery: ProofDiscovery,
  fuel: number,
): ProofStep | null {
  const has = (kind: ActionDescriptor['kind']): boolean =>
    discovery.actions.some((action) => action.kind === kind)
  if (has('doubleCutElim')) {
    return { rule: 'doubleCutElim', region: discovery.sel.regions[0]! }
  }
  if (has('vacuousElim')) {
    return { rule: 'vacuousElim', wireId: discovery.sel.wires[0]! }
  }
  if (has('erase')) return erasureStep(diagram, discovery.sel)
  return has('deiterate') ? deiterationStep(diagram, discovery.sel, fuel) : null
}

export function proofConnectionStep(
  diagram: Diagram,
  source: ConnectionEnd,
  target: ConnectionEnd,
  orientation: ProofOrientation,
  _fuel: number,
): ProofStep {
  if (source.wire === target.wire) {
    throw new Error(`line '${source.wire}' is already one identity`)
  }
  const step: ProofStep = {
    rule: 'wireJoin',
    input: { kind: 'iota', a: source.wire, b: target.wire },
  }
  applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
  return step
}

export function relationSeverStep(
  diagram: Diagram,
  scope: RegionId,
  occurrences: readonly ContentOccurrence[],
  orientation: ProofOrientation,
): ProofStep {
  const input: WireSeverInput = {
    kind: 'relation',
    scope,
    occurrences,
  }
  const step: ProofStep = { rule: 'wireSever', input }
  applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
  return step
}

export function relationJoinStep(
  diagram: Diagram,
  wire: WireId,
  content: DiagramWithBoundary,
  parameters: readonly WireId[],
  orientation: ProofOrientation,
): ProofStep {
  const input: WireJoinInput = {
    kind: 'relation',
    wire,
    content,
    parameters,
  }
  const step: ProofStep = { rule: 'wireJoin', input }
  applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
  return step
}

export type ProofMoveControllerOptions = {
  readonly host: HTMLElement
  readonly active: () => boolean
  readonly diagram: () => Diagram
  readonly engine: () => Engine
  readonly viewScale: () => number
  readonly selection: () => readonly Hit[]
  readonly setSelection: (hits: readonly Hit[]) => void
  readonly context: () => ProofContext
  readonly orientation: () => ProofOrientation
  readonly apply: (action: ProofAction) => void
  readonly refuse: (text: string, pointer: Vec2) => void
  readonly theme: () => Theme
  readonly fuel: () => number
  readonly openSpawn: (sample: PointerSample, region: RegionId) => void
}

type CitationCycle = { readonly candidate: CitationCandidate; index: number }

function sameHit(left: Hit, right: Hit): boolean {
  return left.kind === right.kind && left.id === right.id
}

function regionAt(engine: Engine, diagram: Diagram, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (
      Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)
    ) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

export class ProofMoveController {
  readonly #options: ProofMoveControllerOptions
  readonly #document: Document
  readonly #connection: ConnectionDragController
  readonly #copy: CopyDragController
  #menu: HTMLDivElement | null = null
  #cycle: CitationCycle | null = null
  #lastPointer: Vec2 = { x: 0, y: 0 }

  constructor(options: ProofMoveControllerOptions) {
    assertProofContext(options.context())
    this.#options = options
    this.#document = options.host.ownerDocument
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: (source, target, pointer) => {
        this.#lastPointer = pointer
        try {
          this.#commit(proofConnectionStep(
            options.diagram(),
            source,
            target,
            options.orientation(),
            options.fuel(),
          ))
          return true
        } catch (error) {
          options.refuse(error instanceof Error ? error.message : String(error), pointer)
          return false
        }
      },
      refuse: options.refuse,
    })
    this.#copy = new CopyDragController({
      active: options.active,
      sourceDiagram: options.diagram,
      sourceSelection: options.selection,
      sourceEngine: options.engine,
      viewScale: options.viewScale,
      destination: (sample) => ({
        kind: 'proof',
        diagram: options.diagram(),
        region: regionAt(options.engine(), options.diagram(), sample.world),
        orientation: options.orientation(),
        ctx: this.#context(),
      }),
      commit: (plan) => {
        if (plan.kind !== 'proof') throw new Error('proof copy produced an edit plan')
        options.apply(plan.action)
        options.setSelection([])
      },
      refuse: (text, sample) => options.refuse(text, sample.client),
      theme: options.theme,
      sourcePreview: copySelectionPreview,
      destinationPreview: (destination) =>
        copyDestinationPreview(options.engine(), destination.region, options.theme()),
    })
  }

  claim(sample: PointerSample): PointerClaim | null {
    this.#context()
    this.#lastPointer = sample.client
    if (!this.#options.active() || sample.button !== 0) return null
    if (this.#menu !== null) this.#closeMenu()
    if (sample.shiftKey || sample.ctrlKey) return null
    return this.#connection.claim(sample) ?? this.#copy.claim(sample)
  }

  contextMenu(sample: PointerSample): boolean {
    this.#context()
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    this.#closeMenu()
    const selection = this.#options.selection()
    if (
      selection.length > 0
      && (sample.hit === null || !selection.some((hit) => sameHit(hit, sample.hit!)))
    ) return false
    if (selection.length === 0 && (sample.hit === null || sample.hit.kind === 'region')) {
      this.#options.openSpawn(
        sample,
        regionAt(this.#options.engine(), this.#options.diagram(), sample.world),
      )
      return true
    }
    try {
      this.#openMenu(sample, selection.length === 0 && sample.hit !== null ? [sample.hit] : selection)
    } catch (error) {
      this.#options.refuse(
        error instanceof Error ? error.message : String(error),
        sample.client,
      )
    }
    return true
  }

  doubleClick(sample: PointerSample): boolean {
    this.#context()
    if (!this.#options.active() || sample.hit?.kind !== 'node') return false
    const node = this.#options.diagram().nodes[sample.hit.id]
    if (node?.kind !== 'ref') return false
    this.#commit({ rule: 'unfold', nodeId: sample.hit.id })
    return true
  }

  keyDown(sample: KeySample): boolean {
    this.#context()
    if (!this.#options.active() || sample.repeat) return false
    if (sample.key === 'Escape') {
      const active = this.#menu !== null || this.#cycle !== null
      this.cancel()
      return active
    }
    if (this.#cycle !== null) {
      if (sample.key === 'Tab') {
        this.#cycle.index =
          (this.#cycle.index + 1) % this.#cycle.candidate.occurrences!.length
        return true
      }
      if (sample.key === 'Enter') {
        this.#commit(citationStep(
          this.#options.diagram(),
          this.#cycle.candidate,
          this.#cycle.index,
        ))
        this.#cycle = null
        return true
      }
    }
    if (
      sample.key !== 'Delete'
      && sample.key !== 'Backspace'
      && sample.key !== 'w'
      && sample.key !== 'W'
      && sample.key !== 'i'
      && sample.key !== 'I'
    ) return false
    const discovery = discoverProofActions(
      this.#options.diagram(),
      this.#options.selection(),
      this.#context(),
      this.#options.orientation(),
    )
    if (discovery === null) {
      this.#options.refuse(
        this.#options.selection().length === 0
          ? 'select something first'
          : 'this selection spans several regions',
        this.#lastPointer,
      )
      return true
    }
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      try {
        const step = contextualDeleteStep(
          this.#options.diagram(),
          discovery,
          this.#options.fuel(),
        )
        if (step === null) {
          this.#options.refuse('nothing here reads as a deletion', this.#lastPointer)
        } else this.#commit(step)
      } catch (error) {
        this.#options.refuse(
          error instanceof Error ? error.message : String(error),
          this.#lastPointer,
        )
      }
      return true
    }
    if (sample.key === 'i' || sample.key === 'I') {
      if (!discovery.actions.some((action) => action.kind === 'identityInsert')) {
        this.#options.refuse('identity insertion is not valid for this selection', this.#lastPointer)
      } else {
        this.#commit({
          rule: 'identityInsert',
          region: discovery.sel.region,
          wires: discovery.sel.wires,
        })
      }
      return true
    }
    this.#commit({ rule: 'doubleCutIntro', sel: discovery.sel })
    return true
  }

  overlay(): readonly Shape[] {
    this.#context()
    const result: Shape[] = [...this.#connection.overlay(), ...this.#copy.overlay()]
    const cycle = this.#cycle
    if (cycle !== null && cycle.candidate.occurrences !== null) {
      const occurrence = cycle.candidate.occurrences[cycle.index]!
      for (const node of occurrence.nodeMap.values()) {
        const body = this.#options.engine().bodies.get(node)
        if (body !== undefined) {
          result.push({
            kind: 'circle',
            center: body.pos,
            r: body.discR * this.#options.engine().scale + 1.5,
            fill: null,
            stroke: '#7c3aed',
            width: 2.6,
            insetColor: null,
            glow: null,
          })
        }
      }
    }
    return result
  }

  cancel(): void {
    this.#context()
    this.#closeMenu()
    this.#cycle = null
    this.#connection.cancel()
    this.#copy.cancel()
  }

  dispose(): void {
    this.cancel()
    this.#copy.dispose()
  }

  modifiersChanged(ctrlHeld: boolean): void {
    this.#context()
    this.#copy.modifiersChanged(ctrlHeld)
  }

  #commit(step: ProofStep): void {
    try {
      this.#options.apply(singleStepAction(
        step.rule === 'theorem' ? `cite ${step.name}` : step.rule,
        step,
      ))
      this.#options.setSelection([])
      this.#closeMenu()
    } catch (error) {
      this.#options.refuse(
        error instanceof Error ? error.message : String(error),
        this.#lastPointer,
      )
    }
  }

  #openMenu(sample: PointerSample, hits: readonly Hit[]): void {
    const menu = this.#document.createElement('div')
    menu.className = 'vpa-proof-menu'
    menu.setAttribute('role', 'menu')
    menu.style.cssText = `position:fixed;left:${sample.client.x + 10}px;top:${sample.client.y + 10}px;z-index:31;width:270px;max-height:380px;overflow:auto;border:1.5px solid #d97706;border-radius:8px;background:#fff;box-shadow:0 4px 16px #0003;font:13px system-ui`
    const row = (label: string, run: (() => void) | null): void => {
      const element = this.#document.createElement(run === null ? 'div' : 'button')
      element.textContent = label
      element.className = run === null ? 'vpa-proof-heading' : 'vpa-proof-action'
      element.style.cssText = `display:block;width:100%;box-sizing:border-box;padding:6px 10px;border:0;background:#fff;text-align:left;${run === null ? 'color:#78716c;font-size:10px;text-transform:uppercase' : 'cursor:pointer'}`
      if (run !== null) {
        element.addEventListener('click', () => {
          try {
            run()
          } catch (error) {
            this.#options.refuse(
              error instanceof Error ? error.message : String(error),
              this.#lastPointer,
            )
          }
        })
      }
      menu.append(element)
    }
    const diagram = this.#options.diagram()
    const region = regionAt(this.#options.engine(), diagram, sample.world)
    const context = this.#context()
    const discovery = discoverProofActions(
      diagram,
      hits,
      context,
      this.#options.orientation(),
    )
    if (discovery !== null) {
      row('Actions', null)
      for (const action of discovery.actions) {
        this.#appendAction(row, action, discovery.sel)
      }
    }
    const candidates = citationCandidates(
      diagram,
      hits,
      discovery?.sel.region ?? region,
      context,
      this.#options.orientation(),
      this.#options.fuel(),
    )
    const citations = hits.length === 0
      ? { applicable: [], closed: candidates.closed }
      : candidates
    if (citations.applicable.length > 0) {
      row('Applicable theorems', null)
      for (const candidate of citations.applicable) {
        row(candidate.name, () => this.#beginCitation(candidate))
      }
    }
    if (citations.closed.length > 0) {
      row('Closed theorems', null)
      for (const candidate of citations.closed) {
        row(candidate.name, () => this.#commit(
          citationStep(diagram, candidate, undefined, region),
        ))
      }
    }
    if (menu.childElementCount === 0) return
    this.#menu = menu
    this.#options.host.append(menu)
  }

  #appendAction(
    row: (label: string, run: (() => void) | null) => void,
    action: ActionDescriptor,
    selection: SubgraphSelection,
  ): void {
    switch (action.kind) {
      case 'erase':
        row(action.label, () => this.#commit(erasureStep(this.#options.diagram(), selection)))
        return
      case 'doubleCutWrap':
        row(action.label, () => this.#commit({ rule: 'doubleCutIntro', sel: selection }))
        return
      case 'doubleCutElim':
        row(action.label, () => this.#commit({
          rule: 'doubleCutElim',
          region: selection.regions[0]!,
        }))
        return
      case 'identityInsert':
        row(action.label, () => this.#commit({
          rule: 'identityInsert',
          region: selection.region,
          wires: selection.wires,
        }))
        return
      case 'vacuousElim':
        row(action.label, () => this.#commit({
          rule: 'vacuousElim',
          wireId: selection.wires[0]!,
        }))
        return
      case 'deiterate':
        row(action.label, () => this.#commit(deiterationStep(
          this.#options.diagram(),
          selection,
          this.#options.fuel(),
        )))
        return
      case 'relUnfold':
        row(action.label, () => this.#commit({
          rule: 'unfold',
          nodeId: selection.nodes[0]!,
        }))
        return
      case 'relFold':
        row('Fold into', null)
        for (const [name] of this.#context().relations) {
          row(name, () => this.#commit({
            rule: 'fold',
            occurrence: selection,
            args: inferFoldArgs(
              this.#options.diagram(),
              selection,
              name,
              this.#context(),
            ),
            defId: name,
          }))
        }
        return
      case 'relationSever':
      case 'relationJoin':
        row(action.label, null)
        return
      case 'iterate':
      case 'citeTheorem':
        return
    }
  }

  #beginCitation(candidate: CitationCandidate): void {
    if (candidate.occurrences === null) return
    this.#closeMenu()
    if (candidate.occurrences.length === 1) {
      this.#commit(citationStep(this.#options.diagram(), candidate, 0))
    } else this.#cycle = { candidate, index: 0 }
  }

  #closeMenu(): void {
    this.#menu?.remove()
    this.#menu = null
  }

  #context(): ProofContext {
    const context = this.#options.context()
    assertProofContext(context)
    return context
  }
}
