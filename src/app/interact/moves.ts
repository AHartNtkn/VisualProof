import type { Diagram, Endpoint, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import { derivedScope } from '../../kernel/diagram/regions'
import { IOTA, relSig, type Sig } from '../../kernel/diagram/sig'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../kernel/proof/action'
import { applyStep, type ProofStep } from '../../kernel/proof/step'
import type { ProofContext } from '../../kernel/proof/context'
import { EMPTY_PROOF_CONTEXT, assertProofContext } from '../../kernel/proof/context'
import { bareWireDeletionSteps, bareWireInsertSteps } from '../../kernel/proof/bare-wire'
import { findDeiterationEvidence } from '../../kernel/rules/iteration'
import { termNodeAt, wireAt } from '../../kernel/rules/access'
import { mapTermToCommonCarrier } from '../../kernel/rules/lambda'
import { convertible } from '../../kernel/term/convert'
import type { ConversionCertificate } from '../../kernel/term/certificate'
import { parseTerm } from '../../kernel/term/parse'
import { pkey, type Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import {
  applicableActions,
  type ActionDescriptor,
} from '../actions'
import { inferFoldArgs } from '../define'
import {
  convertToHeadNormal,
  convertToNormal,
  convertToWeakHeadNormal,
} from '../tactics'
import { absorbHits, orphanedWires } from '../edit'
import { buildSelection, regionAt, wireManipulationHitTest, type Hit } from '../hittest'
import { citationCandidates, citationStep, type CitationCandidate } from './cite'
import { CopyDragController } from './copy'
import { ConnectionDragController, type ConnectionEnd } from './connection'
import { FissionDragController, type FissionRequest } from './fission'
import { IdentityOpsController } from './identity-ops'
import { SlashController } from './slash'
import { WireOpsDragController } from './wire-ops'
import { copyDestinationPreview, copySelectionPreview } from './copy-view'
import type { KeySample, PointerClaim, PointerSample } from './viewport'

export type ProofOrientation = 'forward' | 'backward'

/** Slot correspondence whose shared columns are already carried by one wire. */
export function proposeAttachedSlotCorrespondence(
  diagram: Diagram,
  a: NodeId,
  b: NodeId,
) {
  const left = termNodeAt(diagram, a)
  const right = termNodeAt(diagram, b)
  const columnByWire = new Map<WireId, number>()
  const columns = (node: NodeId, arity: number): number[] =>
    Array.from({ length: arity }, (_, slot) => {
      const wire = wireAt(diagram, node, { kind: 'free', index: slot })
      let column = columnByWire.get(wire)
      if (column === undefined) {
        column = columnByWire.size
        columnByWire.set(wire, column)
      }
      return column
    })
  const leftColumns = columns(a, left.freeArity)
  const rightColumns = columns(b, right.freeArity)
  return {
    commonArity: columnByWire.size,
    left: leftColumns,
    right: rightColumns,
  }
}

function outputNodes(diagram: Diagram, wire: WireId): NodeId[] {
  return diagram.wires[wire]!.endpoints
    .filter((endpoint) =>
      endpoint.port.kind === 'output'
      && diagram.nodes[endpoint.node]?.kind === 'term')
    .map((endpoint) => endpoint.node)
}

/** Resolve a term connection gesture to one dedicated replayable Lambda step. */
export function proofConnectionStep(
  diagram: Diagram,
  source: ConnectionEnd,
  target: ConnectionEnd,
  orientation: ProofOrientation,
  fuel: number,
): ProofStep {
  if (source.wire === target.wire) {
    const a = source.endpoint
    const b = target.endpoint
    if (
      a === null
      || b === null
      || a.port.kind !== 'output'
      || b.port.kind !== 'output'
      || a.node === b.node
      || diagram.nodes[a.node]?.kind !== 'term'
      || diagram.nodes[b.node]?.kind !== 'term'
    ) {
      throw new Error("release on another term's output strand to compare arguments")
    }
    const step: ProofStep = {
      rule: 'lambdaHeadStrip',
      a: a.node,
      b: b.node,
      correspondence: proposeAttachedSlotCorrespondence(diagram, a.node, b.node),
    }
    applyStep(diagram, step, EMPTY_PROOF_CONTEXT, orientation)
    return step
  }

  const candidates: ProofStep[] = [{
    rule: 'wireJoin',
    input: { a: source.wire, b: target.wire },
  }]
  const concreteOutput = (end: ConnectionEnd): NodeId | null =>
    end.endpoint?.port.kind === 'output'
    && diagram.nodes[end.endpoint.node]?.kind === 'term'
      ? end.endpoint.node
      : null
  const sourceNode = concreteOutput(source)
  const targetNode = concreteOutput(target)
  const leftCandidates = sourceNode === null
    ? outputNodes(diagram, source.wire)
    : [sourceNode]
  const rightCandidates = targetNode === null
    ? outputNodes(diagram, target.wire)
    : [targetNode]
  const unambiguous = leftCandidates.length === 1 && rightCandidates.length === 1
  const convertiblePairs: Array<{
    readonly a: NodeId
    readonly b: NodeId
    readonly certificate: ConversionCertificate
  }> = []
  if (unambiguous) {
    for (const a of leftCandidates) for (const b of rightCandidates) {
      const left = termNodeAt(diagram, a)
      const right = termNodeAt(diagram, b)
      const correspondence = proposeAttachedSlotCorrespondence(diagram, a, b)
      const result = convertible(
        mapTermToCommonCarrier(left.term, correspondence.left),
        mapTermToCommonCarrier(right.term, correspondence.right),
        fuel,
      )
      if (result.status !== 'convertible') continue
      convertiblePairs.push({ a, b, certificate: result.certificate })
      candidates.push({
        rule: 'lambdaCongruenceJoin',
        a,
        b,
        certificate: result.certificate,
        correspondence,
      })
    }
  }
  for (const pair of convertiblePairs) {
    candidates.push({
      rule: 'lambdaAnchoredWireContract',
      redundant: pair.a,
      survivor: pair.b,
      certificate: pair.certificate,
    })
    candidates.push({
      rule: 'lambdaAnchoredWireContract',
      redundant: pair.b,
      survivor: pair.a,
      certificate: {
        leftSteps: pair.certificate.rightSteps,
        rightSteps: pair.certificate.leftSteps,
      },
    })
  }
  for (const candidate of candidates) {
    try {
      applyStep(diagram, candidate, EMPTY_PROOF_CONTEXT, orientation)
      return candidate
    } catch {
      // Several proof justifications can yield the same visible merge.
    }
  }
  if (!unambiguous && (leftCandidates.length > 1 || rightCandidates.length > 1)) {
    throw new Error(
      'proof connection is ambiguous; drag from one producer output strand to the other',
    )
  }
  throw new Error(
    `no valid proof connection joins lines '${source.wire}' and '${target.wire}'`,
  )
}

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
    .filter((wire) => !existing.has(wire) && derivedScope(diagram, wire) === selection.region)
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
): ProofStep {
  const evidence = findDeiterationEvidence(diagram, selection)
  return {
    rule: 'deiteration',
    sel: selection,
    ...evidence,
  }
}

export function contextualDeleteSteps(
  diagram: Diagram,
  discovery: ProofDiscovery,
): readonly ProofStep[] | null {
  const has = (kind: ActionDescriptor['kind']): boolean =>
    discovery.actions.some((action) => action.kind === kind)
  if (has('doubleCutElim')) {
    return [{ rule: 'doubleCutElim', region: discovery.sel.regions[0]! }]
  }
  if (has('vacuityDelete')) {
    return bareWireDeletionSteps(diagram, discovery.sel.wires[0]!)
  }
  if (has('erase')) return [erasureStep(diagram, discovery.sel)]
  return has('deiterate') ? [deiterationStep(diagram, discovery.sel)] : null
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
  readonly commitFission: (request: FissionRequest) => void
  readonly refuse: (text: string, pointer: Vec2) => void
  readonly theme: () => Theme
  readonly fuel: () => number
  readonly openSpawn: (sample: PointerSample, region: RegionId) => void
}

type CitationCycle = { readonly candidate: CitationCandidate; index: number }

function sameHit(left: Hit, right: Hit): boolean {
  return left.kind === right.kind && left.id === right.id
}

export class ProofMoveController {
  readonly #options: ProofMoveControllerOptions
  readonly #document: Document
  readonly #identity: IdentityOpsController
  readonly #connection: ConnectionDragController
  readonly #fission: FissionDragController
  readonly #wireOps: WireOpsDragController
  readonly #copy: CopyDragController
  readonly #slash: SlashController
  #prompt: HTMLDivElement | null = null
  #menu: HTMLDivElement | null = null
  #cycle: CitationCycle | null = null
  #lastPointer: Vec2 = { x: 0, y: 0 }
  #lastWorld: Vec2 | null = null

  constructor(options: ProofMoveControllerOptions) {
    assertProofContext(options.context())
    this.#options = options
    this.#document = options.host.ownerDocument
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      acceptSource: (source) => source.endpoint !== null
        && options.diagram().nodes[source.endpoint.node]?.kind === 'term'
        && (source.endpoint.port.kind === 'output' || source.endpoint.port.kind === 'free'),
      commit: (gesture, pointer) => {
        this.#lastPointer = pointer
        try {
          if ('identity' in gesture.target) {
            throw new Error('term connections land on a line, not an identity dot')
          }
          return this.#commit(proofConnectionStep(
            options.diagram(),
            gesture.source,
            gesture.target,
            options.orientation(),
            options.fuel(),
          ))
        } catch (error) {
          options.refuse(
            error instanceof Error ? error.message : String(error),
            pointer,
          )
          return false
        }
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
      refuse: options.refuse,
    })
    this.#identity = new IdentityOpsController({
      active: options.active,
      engine: options.engine,
      diagram: options.diagram,
      viewScale: options.viewScale,
      theme: options.theme,
      claimEndDiscs: false,
      selected: (node) => options.selection().some((hit) => hit.kind === 'node' && hit.id === node),
      commit: (label, steps, pointer) => {
        this.#lastPointer = pointer
        return this.#commitSteps(label, steps)
      },
      refuse: options.refuse,
    })
    this.#wireOps = new WireOpsDragController({
      active: options.active,
      engine: options.engine,
      diagram: options.diagram,
      viewScale: options.viewScale,
      theme: options.theme,
      context: () => this.#context(),
      orientation: options.orientation,
      commit: (label, steps, pointer) => {
        this.#lastPointer = pointer
        return this.#commitSteps(label, steps)
      },
      promptSig: (client, apply) => { this.#promptSig(client, apply) },
      refuse: options.refuse,
    })
    this.#slash = new SlashController({
      active: options.active,
      engine: options.engine,
      diagram: options.diagram,
      theme: options.theme,
      commit: (crossings, sample) => {
        const diagram = options.diagram()
        const byWire = new Map<WireId, Endpoint[]>()
        for (const crossing of crossings) {
          const bucket = byWire.get(crossing.wire) ?? []
          bucket.push(crossing.endpoint)
          byWire.set(crossing.wire, bucket)
        }
        const steps: ProofStep[] = [...byWire.entries()].map(([wire, severed]) => {
          const moved = new Set(severed.map((ep) => `${ep.node}:${pkey(ep.port)}`))
          const keep = (diagram.wires[wire]?.endpoints ?? [])
            .filter((ep) => !moved.has(`${ep.node}:${pkey(ep.port)}`))
          return { rule: 'wireSever', input: { wire, keep } }
        })
        this.#lastPointer = sample.client
        this.#commitSteps('wireSever', steps)
      },
      still: (sample) => { this.#openContextMenu(sample) },
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

  /** Track the hovered world point for pointer-located keyboard actions. */
  passiveSample(sample: PointerSample | null): void {
    if (sample === null) {
      this.#lastWorld = null
      this.#fission.hover(null)
      return
    }
    this.#lastPointer = sample.client
    this.#lastWorld = sample.world
    this.#fission.hover(this.#copy.dragging ? null : sample)
  }

  claim(sample: PointerSample): PointerClaim | null {
    this.#context()
    this.#lastPointer = sample.client
    if (
      !this.#options.active()
      || (sample.button !== 0 && sample.button !== 2)
    ) return null
    if (this.#menu !== null) this.#closeMenu()
    if (sample.shiftKey || sample.ctrlKey) return null
    if (sample.button === 2) return this.#slash.claim(sample)
    const claim = this.#identity.claim(sample)
      ?? this.#connection.claim(sample)
      ?? this.#fission.claim(sample)
      ?? this.#wireOps.claim(sample)
      ?? this.#copy.claim(sample)
    if (claim !== null && this.#copy.dragging) this.#fission.hover(null)
    return claim
  }

  contextMenu(sample: PointerSample): boolean {
    this.#context()
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    // Every claimed right press suppresses the browser's contextmenu event
    // (it can fire at press time); a still release reopens through the
    // slash's still callback, so the palette appears exactly once for a
    // plain click.
    if (this.#slash.consumeMenuSuppression()) return true
    return this.#openContextMenu(sample)
  }

  #openContextMenu(sample: PointerSample): boolean {
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
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    if (sample.hit?.kind === 'wire') {
      this.#commit({ rule: 'lambdaFusion', wire: sample.hit.id })
      return true
    }
    if (sample.hit?.kind !== 'node') return false
    const node = this.#options.diagram().nodes[sample.hit.id]
    if (node?.kind === 'ref') {
      this.#commit({ rule: 'unfold', nodeId: sample.hit.id })
      return true
    }
    if (node?.kind !== 'term') return false
    try {
      this.#commit(convertToNormal(
        this.#options.diagram(),
        sample.hit.id,
        this.#options.fuel(),
      ).step)
    } catch (error) {
      this.#options.refuse(
        error instanceof Error ? error.message : String(error),
        sample.client,
      )
    }
    return true
  }

  keyDown(sample: KeySample): boolean {
    this.#context()
    if (!this.#options.active() || sample.repeat) return false
    if (sample.key === 'Escape') {
      const active = this.#menu !== null
        || this.#cycle !== null
        || this.#prompt !== null
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
    // Q spawns a bare quantifier wire — the two-pin segment — at the region
    // under the pointer; Shift+Q spawns a proposition quantifier (nullary
    // relation) instead (2026-07-30 rulings: a floating existential is
    // meaningful content — its presence changes the statement, if only
    // trivially — and the nullary spawn seeds every relational signature by
    // application, rim-pull, and extension).
    if (sample.key === 'q' || sample.key === 'Q') {
      if (this.#lastWorld === null) {
        this.#options.refuse('point at a region first', this.#lastPointer)
        return true
      }
      const world = this.#lastWorld
      // Over a strand, Q pins the wire at the hovered region — shift is
      // ignored there, since a pin's sig is the wire's own sig, not a choice
      // the gesture makes.
      const manipulation = wireManipulationHitTest(
        this.#options.engine(), world, { scale: this.#options.viewScale() },
      )
      if (manipulation !== null) {
        this.#commitSteps('vacuity', [{
          rule: 'vacuity',
          direction: 'insert',
          instance: {
            kind: 'pin',
            wire: manipulation.wire,
            node: 'pin',
            region: regionAt(this.#options.engine(), this.#options.diagram(), world),
          },
        }])
        return true
      }
      this.#commitSteps('vacuity', bareWireInsertSteps(
        this.#options.diagram(),
        regionAt(
          this.#options.engine(),
          this.#options.diagram(),
          world,
        ),
        sample.shiftKey ? relSig([]) : IOTA,
        'w',
        ['pin0', 'pin1'],
      ).steps)
      return true
    }
    if (
      (sample.key === 'f' || sample.key === 'F')
      && !sample.ctrlKey
      && !sample.altKey
      && !sample.metaKey
    ) {
      const selection = this.#options.selection()
      if (selection.length !== 1 || selection[0]?.kind !== 'wire') return false
      this.#commit({ rule: 'lambdaFusion', wire: selection[0].id })
      return true
    }
    if (
      sample.key !== 'Delete'
      && sample.key !== 'Backspace'
      && sample.key !== 'w'
      && sample.key !== 'W'
    ) return false
    if (
      (sample.key === 'w' || sample.key === 'W')
      && this.#options.selection().length === 0
    ) {
      // W with nothing highlighted spawns an empty double cut at the region
      // under the pointer (2026-07-10 approved design; 2026-07-30 ruling).
      if (this.#lastWorld === null) {
        this.#options.refuse('point at a region first', this.#lastPointer)
        return true
      }
      this.#commit({
        rule: 'doubleCutIntro',
        sel: {
          region: regionAt(
            this.#options.engine(),
            this.#options.diagram(),
            this.#lastWorld,
          ),
          regions: [],
          nodes: [],
          wires: [],
        },
      })
      return true
    }
    // Delete on a single identity node reads as the vacuity shape it names:
    // a nullary point vanishes outright, a unary node either retracts a stub
    // (its wire's only other end is itself an identity node — the two-end
    // floor means that end can't be a detach target) or detaches as a spare
    // pin. Arity ≥ 2 is content in a path, not apparatus, so it falls
    // through to discovery unchanged.
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      const hits = this.#options.selection()
      if (hits.length === 1 && hits[0]!.kind === 'node') {
        const diagram = this.#options.diagram()
        const node = diagram.nodes[hits[0]!.id]
        if (node?.kind === 'identity') {
          if (node.arity === 0) {
            this.#commit({
              rule: 'vacuity',
              direction: 'delete',
              instance: { kind: 'point', node: hits[0]!.id, region: node.region, sig: node.sig },
            })
            return true
          }
          if (node.arity === 1) {
            const [wireId, wire] = Object.entries(diagram.wires)
              .find(([, w]) => w.endpoints.some((ep) => ep.node === hits[0]!.id))!
            const other = wire.endpoints.find((ep) => ep.node !== hits[0]!.id)
            const stubShaped = wire.endpoints.length === 2
              && other !== undefined
              && diagram.nodes[other.node]?.kind === 'identity'
            this.#commit(stubShaped
              ? {
                  rule: 'vacuity',
                  direction: 'delete',
                  instance: {
                    kind: 'stub', base: other.node, wire: wireId, end: hits[0]!.id,
                    region: node.region,
                  },
                }
              : {
                  rule: 'vacuity',
                  direction: 'delete',
                  instance: { kind: 'pin', wire: wireId, node: hits[0]!.id, region: node.region },
                })
            return true
          }
        }
      }
    }
    // Delete on a lone attached wire deletes its ends; the wire itself
    // stays, quantified. This never forms a subgraph selection (the ends
    // stay behind), so it dispatches before discovery.
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      const hits = this.#options.selection()
      if (hits.length === 1 && hits[0]!.kind === 'wire') {
        const wire = this.#options.diagram().wires[hits[0]!.id]
        if (wire !== undefined && wire.endpoints.length > 0) {
          this.#commit({ rule: 'endsDelete', wire: hits[0]!.id })
          return true
        }
      }
    }
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
        const steps = contextualDeleteSteps(
          this.#options.diagram(),
          discovery,
        )
        if (steps === null) {
          this.#options.refuse('nothing here reads as a deletion', this.#lastPointer)
        } else this.#commitSteps('delete', steps)
      } catch (error) {
        this.#options.refuse(
          error instanceof Error ? error.message : String(error),
          this.#lastPointer,
        )
      }
      return true
    }
    this.#commit({ rule: 'doubleCutIntro', sel: discovery.sel })
    return true
  }

  overlay(): readonly Shape[] {
    this.#context()
    const result: Shape[] = [
      ...this.#identity.overlay(),
      ...this.#connection.overlay(),
      ...this.#fission.overlay(),
      ...this.#wireOps.overlay(),
      ...this.#copy.overlay(),
      ...this.#slash.overlay(),
    ]
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
    this.#closePrompt()
    this.#identity.cancel()
    this.#connection.cancel()
    this.#fission.cancel()
    this.#wireOps.cancel()
    this.#copy.cancel()
    this.#slash.cancel()
  }

  dispose(): void {
    this.cancel()
    this.#fission.dispose()
    this.#copy.dispose()
  }

  modifiersChanged(ctrlHeld: boolean): void {
    this.#context()
    this.#fission.modifiersChanged(ctrlHeld)
    this.#copy.modifiersChanged(ctrlHeld)
  }

  #commit(step: ProofStep): boolean {
    return this.#commitSteps(
      step.rule === 'theorem' ? `cite ${step.name}` : step.rule,
      [step],
    )
  }

  #commitSteps(label: string, steps: readonly ProofStep[]): boolean {
    try {
      this.#options.apply({ label, steps, placements: [] })
      this.#options.setSelection([])
      this.#closeMenu()
      return true
    } catch (error) {
      this.#options.refuse(
        error instanceof Error ? error.message : String(error),
        this.#lastPointer,
      )
      return false
    }
  }

  #openMenu(sample: PointerSample, hits: readonly Hit[]): void {
    const menu = this.#document.createElement('div')
    menu.className = 'vpa-proof-menu'
    menu.setAttribute('role', 'menu')
    menu.style.left = `${sample.client.x + 10}px`
    menu.style.top = `${sample.client.y + 10}px`
    const row = (label: string, run: (() => void) | null): void => {
      const element = this.#document.createElement(run === null ? 'div' : 'button')
      element.textContent = label
      element.className = run === null ? 'vpa-proof-heading' : 'vpa-proof-action'
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
      // Rules with dedicated direct gestures never appear as menu rows
      // (unfold has double-click). Fold and citation remain: choosing a
      // stored name is inherently a picker — the diagram cannot determine
      // it — so these rows are the interface, not debt.
      const paletteRows = discovery.actions.filter((action) =>
        action.kind === 'convert'
        || action.kind === 'relFold'
        || action.kind === 'citeTheorem')
      if (paletteRows.length > 0) row('Actions', null)
      for (const action of paletteRows) {
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
      case 'vacuityDelete':
        row(action.label, () => this.#commitSteps(
          'vacuity',
          bareWireDeletionSteps(this.#options.diagram(), selection.wires[0]!),
        ))
        return
      case 'deiterate':
        row(action.label, () => this.#commit(deiterationStep(
          this.#options.diagram(),
          selection,
        )))
        return
      case 'convert':
        this.#appendConversions(row, selection.nodes[0]!)
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
      case 'iterate':
      case 'relUnfold':
      case 'citeTheorem':
        return
    }
  }

  #appendConversions(
    row: (label: string, run: (() => void) | null) => void,
    node: NodeId,
  ): void {
    row('Convert → normal', () => this.#commit(convertToNormal(
      this.#options.diagram(), node, this.#options.fuel(),
    ).step))
    row('Convert → head normal', () => this.#commit(convertToHeadNormal(
      this.#options.diagram(), node, this.#options.fuel(),
    ).step))
    row('Convert → weak head normal', () => this.#commit(convertToWeakHeadNormal(
      this.#options.diagram(), node, this.#options.fuel(),
    ).step))
    row('Convert → custom target…', () => this.#openTextPrompt(
      'Conversion target',
      'target term',
      (value) => {
        const parsed = parseTerm(value)
        const diagram = this.#options.diagram()
        const source = termNodeAt(diagram, node)
        if (parsed.freeIdentifiers.length > source.freeArity) {
          throw new Error(
            `conversion target uses ${parsed.freeIdentifiers.length} free slots, `
            + `but the source interface has ${source.freeArity}`,
          )
        }
        const assigned = parsed.freeIdentifiers.map((identifier) => {
          const match = /^f(0|[1-9][0-9]*)$/u.exec(identifier)
          if (match === null) return undefined
          const slot = Number(match[1])
          if (slot >= source.freeArity) {
            throw new Error(
              `conversion target free identifier '${identifier}' is outside `
              + `the source interface 0..<${source.freeArity}`,
            )
          }
          return slot
        })
        const used = new Set(assigned.filter(
          (slot): slot is number => slot !== undefined,
        ))
        if (used.size !== assigned.filter((slot) => slot !== undefined).length) {
          throw new Error('conversion target maps two free identifiers to one source slot')
        }
        let next = 0
        const mapping = assigned.map((slot) => {
          if (slot !== undefined) return slot
          while (used.has(next)) next++
          if (next >= source.freeArity) {
            throw new Error('conversion target has no available source free slot')
          }
          used.add(next)
          return next++
        })
        const target = mapTermToCommonCarrier(parsed.term, mapping)
        const conversion = convertible(
          source.term,
          target,
          this.#options.fuel(),
        )
        if (conversion.status === 'fuel-exhausted') {
          throw new Error(conversion.detail)
        }
        if (conversion.status === 'not-convertible') {
          throw new Error('conversion target is not beta-eta convertible to the source term')
        }
        const slots = Array.from(
          { length: source.freeArity },
          (_, slot) => slot,
        )
        this.#commit({
          rule: 'lambdaConversion',
          node,
          term: target,
          correspondence: {
            commonArity: source.freeArity,
            left: slots,
            right: [...slots],
          },
          certificate: conversion.certificate,
          attachments: {},
        })
      },
    ))
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

  #openTextPrompt(
    label: string,
    placeholder: string,
    accept: (value: string) => void,
  ): void {
    this.#closePrompt()
    const wrap = this.#document.createElement('div')
    wrap.className = 'vpa-proof-prompt'
    wrap.style.left = `${this.#lastPointer.x + 10}px`
    wrap.style.top = `${this.#lastPointer.y + 10}px`
    const input = this.#document.createElement('input')
    input.type = 'text'
    input.placeholder = placeholder
    input.setAttribute('aria-label', label)
    input.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') {
        this.#closePrompt()
        return
      }
      if (event.key !== 'Enter') return
      try {
        accept(input.value)
        this.#closePrompt()
      } catch (error) {
        this.#options.refuse(
          error instanceof Error ? error.message : String(error),
          this.#lastPointer,
        )
      }
    })
    wrap.append(input)
    this.#prompt = wrap
    this.#options.host.append(wrap)
    queueMicrotask(() => input.focus())
  }

  /** The arity prompt: blank means an individual (ι); n means rel(ιⁿ). */
  #promptSig(client: Vec2, apply: (sig: Sig) => void): void {
    this.#closePrompt()
    const box = this.#document.createElement('div')
    box.className = 'vpa-proof-prompt'
    box.style.left = `${client.x + 10}px`
    box.style.top = `${client.y + 10}px`
    const input = this.#document.createElement('input')
    input.type = 'text'
    input.placeholder = 'arity (blank = individual)'
    input.setAttribute('aria-label', "New position's arity")
    input.style.cssText = 'width:170px;box-sizing:border-box'
    box.append(input)
    input.addEventListener('keydown', (event) => {
      if (event.key === 'Escape') {
        this.#closePrompt()
        return
      }
      if (event.key !== 'Enter') return
      const raw = input.value.trim()
      const arity = raw === '' ? null : Number(raw)
      if (arity !== null && (!Number.isInteger(arity) || arity < 0)) {
        this.#options.refuse('enter a non-negative arity or leave blank', client)
        return
      }
      this.#closePrompt()
      apply(arity === null
        ? IOTA
        : relSig(Array.from({ length: arity }, () => IOTA)))
    })
    this.#options.host.append(box)
    this.#prompt = box
    input.focus()
  }

  #closePrompt(): void {
    this.#prompt?.remove()
    this.#prompt = null
  }

  #context(): ProofContext {
    const context = this.#options.context()
    assertProofContext(context)
    return context
  }
}
