import { DiagramBuilder } from '../../kernel/diagram/builder'
import type { Diagram, NodeId, RegionId, WireId } from '../../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../../kernel/diagram/boundary'
import type { SubgraphSelection } from '../../kernel/diagram/subgraph/selection'
import { singleStepAction, type ProofAction } from '../../kernel/proof/action'
import { applyStep, type ProofContext, type ProofStep } from '../../kernel/proof/step'
import { convertible } from '../../kernel/term/convert'
import type { ConversionCertificate } from '../../kernel/term/certificate'
import { parseTerm } from '../../kernel/term/parse'
import { applyConversion } from '../../kernel/rules/conversion'
import { findDeiterationEvidence } from '../../kernel/rules/iteration'
import { termNodeAt, wireAt } from '../../kernel/rules/access'
import { mapTermToCommonCarrier, proposePortCorrespondence } from '../../kernel/rules/port-correspondence'
import type { PortCorrespondence } from '../../kernel/rules/port-correspondence'
import type { Engine } from '../../view/engine'
import type { Shape, Theme } from '../../view/paint'
import type { Vec2 } from '../../view/vec'
import { applicableActions, type ActionDescriptor } from '../actions'
import { inferFoldArgs } from '../define'
import { absorbHits, orphanedWires } from '../edit'
import { buildSelection, type Hit } from '../hittest'
import { convertToHeadNormal, convertToWeakHeadNormal } from '../tactics'
import { citationCandidates, citationStep, type CitationCandidate } from './cite'
import { ConnectionDragController, type ConnectionEnd } from './connection'
import type { KeySample, PointerClaim, PointerSample } from './viewport'
import { FissionDragController, type FissionRequest } from './fission'
import { CopyDragController, copyDestinationPreview } from './copy'

export type ProofOrientation = 'forward' | 'backward'

/** Author a correspondence whose shared columns already satisfy the kernel's
 * attachment gate. Declared ports on different wires become one-sided. */
function proposeAttachedPortCorrespondence(d: Diagram, a: NodeId, b: NodeId): PortCorrespondence {
  const leftNode = termNodeAt(d, a)
  const rightNode = termNodeAt(d, b)
  const left = new Map<string, number>()
  const right = new Map<string, number>()
  const usedRight = new Set<string>()
  let commonArity = 0
  for (const leftName of leftNode.freePorts) {
    const leftWire = wireAt(d, a, { kind: 'freeVar', name: leftName })
    const rightName = rightNode.freePorts.find((candidate) =>
      !usedRight.has(candidate)
      && wireAt(d, b, { kind: 'freeVar', name: candidate }) === leftWire)
    if (rightName === undefined) continue
    left.set(leftName, commonArity)
    right.set(rightName, commonArity)
    usedRight.add(rightName)
    commonArity++
  }
  for (const name of leftNode.freePorts) if (!left.has(name)) left.set(name, commonArity++)
  for (const name of rightNode.freePorts) if (!right.has(name)) right.set(name, commonArity++)
  return { commonArity, left: Object.fromEntries(left), right: Object.fromEntries(right) }
}

export type InstantiationChoice =
  | { readonly kind: 'anonymous'; readonly label: 'New relation…' }
  | { readonly kind: 'named'; readonly label: string; readonly name: string }

export function instantiationChoices(ctx: ProofContext, arity: number): readonly InstantiationChoice[] {
  const choices: InstantiationChoice[] = [{ kind: 'anonymous', label: 'New relation…' }]
  for (const [name, relation] of ctx.relations) {
    if (relation.boundary.length === arity) choices.push({ kind: 'named', label: name, name })
  }
  return choices
}

export type ProofDiscovery = {
  readonly sel: SubgraphSelection
  readonly actions: readonly ActionDescriptor[]
}

export function discoverProofActions(
  d: Diagram,
  hits: readonly Hit[],
  ctx: ProofContext,
  orientation: ProofOrientation,
): ProofDiscovery | null {
  if (hits.length === 0) return null
  try {
    const sel = buildSelection(d, absorbHits(d, hits))
    return { sel, actions: applicableActions(d, sel, ctx, orientation === 'backward') }
  } catch {
    return null
  }
}

function erasureSelection(d: Diagram, sel: SubgraphSelection): SubgraphSelection {
  const existing = new Set(sel.wires)
  const riders = orphanedWires(d, new Set(sel.nodes))
    .filter((wire) => !existing.has(wire) && d.wires[wire]!.scope === sel.region)
  return riders.length === 0 ? sel : { ...sel, wires: [...sel.wires, ...riders] }
}

export function erasureStep(d: Diagram, sel: SubgraphSelection): ProofStep {
  return { rule: 'erasure', sel: erasureSelection(d, sel) }
}

/** Interactive construction of a replayable, fuel-free deiteration step. */
export function deiterationStep(d: Diagram, sel: SubgraphSelection, fuel: number): ProofStep {
  const evidence = findDeiterationEvidence(d, sel, fuel)
  return { rule: 'deiteration', sel, ...evidence }
}

export function contextualDeleteStep(d: Diagram, discovery: ProofDiscovery, fuel: number): ProofStep | null {
  const byKind = (kind: ActionDescriptor['kind']): ActionDescriptor | undefined =>
    discovery.actions.find((action) => action.kind === kind)
  const action = byKind('doubleCutElim') ?? byKind('vacuousElim') ?? byKind('erase') ?? byKind('deiterate')
  if (action === undefined) return null
  switch (action.kind) {
    case 'doubleCutElim': return { rule: 'doubleCutElim', region: discovery.sel.regions[0]! }
    case 'vacuousElim': return { rule: 'vacuousElim', region: discovery.sel.regions[0]! }
    case 'erase': return erasureStep(d, discovery.sel)
    case 'deiterate': return deiterationStep(d, discovery.sel, fuel)
    default: throw new Error(`'${action.kind}' is not a contextual deletion`)
  }
}

export function foldedComprehension(ctx: ProofContext, name: string): DiagramWithBoundary {
  const relation = ctx.relations.get(name)
  if (relation === undefined) throw new Error(`unknown relation '${name}'`)
  const arity = relation.boundary.length
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, arity)
  const boundary: WireId[] = []
  for (let index = 0; index < arity; index++) {
    boundary.push(builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index } }]))
  }
  return mkDiagramWithBoundary(builder.build(), boundary)
}

const connectionContext: ProofContext = { theorems: new Map(), relations: new Map() }

function outputNodes(d: Diagram, wire: WireId): NodeId[] {
  return d.wires[wire]!.endpoints
    .filter((endpoint) => endpoint.port.kind === 'output' && d.nodes[endpoint.node]?.kind === 'term')
    .map((endpoint) => endpoint.node)
}

/** Resolve the one graphical connection gesture to a replayable proof record.
    Candidate choice is deterministic but intentionally invisible: every
    accepted different-wire candidate has the same visible merged-wire result. */
export function proofConnectionStep(
  d: Diagram,
  source: ConnectionEnd,
  target: ConnectionEnd,
  orientation: ProofOrientation,
  fuel: number,
): ProofStep {
  if (source.wire === target.wire) {
    const a = source.endpoint
    const b = target.endpoint
    if (a === null || b === null || a.port.kind !== 'output' || b.port.kind !== 'output'
      || a.node === b.node || d.nodes[a.node]?.kind !== 'term' || d.nodes[b.node]?.kind !== 'term') {
      throw new Error("release on another term's output strand to compare arguments")
    }
    const correspondence = proposeAttachedPortCorrespondence(d, a.node, b.node)
    const step: ProofStep = { rule: 'headStrip', a: a.node, b: b.node, correspondence }
    applyStep(d, step, connectionContext, orientation)
    return step
  }

  const candidates: ProofStep[] = [{ rule: 'wireJoin', a: source.wire, b: target.wire }]
  const left = outputNodes(d, source.wire)
  const right = outputNodes(d, target.wire)
  const concreteOutput = (end: ConnectionEnd): NodeId | null => end.endpoint?.port.kind === 'output'
    && d.nodes[end.endpoint.node]?.kind === 'term' ? end.endpoint.node : null
  const sourceNode = concreteOutput(source)
  const targetNode = concreteOutput(target)
  const leftCandidates = sourceNode === null ? left : [sourceNode]
  const rightCandidates = targetNode === null ? right : [targetNode]
  const unambiguous = leftCandidates.length === 1 && rightCandidates.length === 1
  const convertiblePairs: Array<{ readonly a: NodeId; readonly b: NodeId; readonly certificate: ConversionCertificate }> = []
  if (unambiguous) for (const a of leftCandidates) {
    for (const b of rightCandidates) {
      const leftNode = termNodeAt(d, a)
      const rightNode = termNodeAt(d, b)
      const leftTerm = leftNode.term
      const rightTerm = rightNode.term
      const correspondence = proposeAttachedPortCorrespondence(d, a, b)
      const result = convertible(
        mapTermToCommonCarrier(leftTerm, correspondence.left),
        mapTermToCommonCarrier(rightTerm, correspondence.right),
        fuel,
      )
      if (result.status !== 'convertible') continue
      convertiblePairs.push({ a, b, certificate: result.certificate })
      candidates.push({ rule: 'congruenceJoin', a, b, certificate: result.certificate, correspondence })
    }
  }
  for (const pair of convertiblePairs) {
    candidates.push({ rule: 'anchoredWireContract', redundant: pair.a, survivor: pair.b, certificate: pair.certificate })
    candidates.push({
      rule: 'anchoredWireContract', redundant: pair.b, survivor: pair.a,
      certificate: { leftSteps: pair.certificate.rightSteps, rightSteps: pair.certificate.leftSteps },
    })
  }
  for (const candidate of candidates) {
    try {
      applyStep(d, candidate, connectionContext, orientation)
      return candidate
    } catch {
      // Another proof justification may license the same visible connection.
    }
  }
  if (!unambiguous && (leftCandidates.length > 1 || rightCandidates.length > 1)) {
    throw new Error('proof connection is ambiguous; drag from one producer output strand to the other')
  }
  throw new Error(`no valid proof connection joins lines '${source.wire}' and '${target.wire}'`)
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
  readonly openComprehension: (bubble: RegionId, pointer: Vec2) => void
  readonly openAbstraction: (selection: SubgraphSelection, pointer: Vec2) => void
  readonly openSpawn: (sample: PointerSample, region: RegionId) => void
}

type CitationCycle = { readonly candidate: CitationCandidate; index: number }

function sameHit(a: Hit, b: Hit): boolean {
  return a.kind === b.kind && a.id === b.id
}

function regionAt(engine: Engine, diagram: Diagram, point: Vec2): RegionId {
  let best: { readonly id: RegionId; readonly radius: number } | null = null
  for (const [id, geometry] of engine.regions) {
    if (diagram.regions[id]?.kind === 'sheet') continue
    if (Math.hypot(point.x - geometry.center.x, point.y - geometry.center.y) <= geometry.radius
      && (best === null || geometry.radius < best.radius)) best = { id, radius: geometry.radius }
  }
  return best?.id ?? diagram.root
}

export class ProofMoveController {
  readonly #options: ProofMoveControllerOptions
  readonly #document: Document
  readonly #connection: ConnectionDragController
  readonly #fission: FissionDragController
  readonly #copy: CopyDragController
  #menu: HTMLDivElement | null = null
  #prompt: HTMLDivElement | null = null
  #cycle: CitationCycle | null = null
  #lastPointer: Vec2

  constructor(options: ProofMoveControllerOptions) {
    this.#options = options
    this.#document = options.host.ownerDocument
    this.#lastPointer = { x: 0, y: 0 }
    this.#connection = new ConnectionDragController({
      active: options.active,
      engine: options.engine,
      viewScale: options.viewScale,
      theme: options.theme,
      commit: (source, target, pointer) => {
        this.#lastPointer = pointer
        try {
          this.#commit(proofConnectionStep(
            this.#options.diagram(), source, target,
            this.#options.orientation(), this.#options.fuel(),
          ))
          return true
        } catch (error) {
          this.#options.refuse(error instanceof Error ? error.message : String(error), pointer)
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
    this.#copy = new CopyDragController({
      active: options.active,
      sourceDiagram: options.diagram,
      sourceSelection: options.selection,
      sourceEngine: options.engine,
      viewScale: options.viewScale,
      destination: (sample) => ({
        kind: 'proof', diagram: options.diagram(),
        region: regionAt(options.engine(), options.diagram(), sample.world),
        orientation: options.orientation(), ctx: options.context(),
      }),
      commit: (plan) => {
        if (plan.kind !== 'proof') throw new Error('proof copy produced a structural plan')
        this.#options.apply(plan.action)
        this.#options.setSelection([])
      },
      refuse: (text, sample) => options.refuse(text, sample.client),
      theme: options.theme,
      destinationPreview: (destination) => copyDestinationPreview(
        options.engine(), destination.region, options.theme(),
      ),
    })
  }

  claim(sample: PointerSample): PointerClaim | null {
    this.#lastPointer = sample.client
    if (!this.#options.active() || sample.button !== 0) return null
    if (this.#cycle !== null && !sample.ctrlKey) {
      const cycle = this.#cycle
      return {
        still: 'claim', blocksPassiveRelaxation: false, move: () => {},
        release: (_next, moved) => {
          if (!moved) cycle.index = (cycle.index + 1) % cycle.candidate.occurrences!.length
        },
        cancel: () => {},
      }
    }
    if (this.#menu !== null) this.#closeMenu()
    if (sample.shiftKey || sample.ctrlKey) return null
    const connection = this.#connection.claim(sample)
    if (connection !== null) return connection
    const fission = this.#fission.claim(sample)
    if (fission !== null) return fission
    const copy = this.#copy.claim(sample)
    if (copy !== null) this.#fission.hover(null)
    return copy
  }

  contextMenu(sample: PointerSample): boolean {
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    this.#closeMenu()
    const selection = this.#options.selection()
    if (selection.length > 0 && (sample.hit === null || !selection.some((hit) => sameHit(hit, sample.hit!)))) return false
    if (selection.length === 0 && (sample.hit === null || sample.hit.kind === 'region')) {
      this.#options.openSpawn(sample, regionAt(this.#options.engine(), this.#options.diagram(), sample.world))
      return true
    }
    try {
      this.#openMenu(sample, selection)
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), sample.client)
    }
    return true
  }

  doubleClick(sample: PointerSample): boolean {
    this.#lastPointer = sample.client
    if (!this.#options.active()) return false
    if (sample.hit?.kind === 'wire') {
      this.#commit({ rule: 'fusion', wire: sample.hit.id })
      return true
    }
    if (sample.hit?.kind !== 'node') return false
    const node = this.#options.diagram().nodes[sample.hit.id]
    if (node?.kind !== 'term') return false
    const fuel = this.#options.fuel()
    try {
      this.#commit(convertToWeakHeadNormal(this.#options.diagram(), sample.hit.id, fuel).step)
    } catch {
      try {
        this.#commit(convertToHeadNormal(this.#options.diagram(), sample.hit.id, fuel).step)
      } catch {
        this.#options.refuse('already in normal form — use Convert → custom target for a specific βη-equal shape', sample.client)
      }
    }
    return true
  }

  keyDown(sample: KeySample): boolean {
    if (!this.#options.active() || sample.repeat) return false
    if (sample.key === 'Escape') {
      const active = this.#menu !== null || this.#prompt !== null || this.#cycle !== null
      this.cancel()
      return active
    }
    if (this.#cycle !== null) {
      if (sample.key === 'Tab') {
        this.#cycle.index = (this.#cycle.index + 1) % this.#cycle.candidate.occurrences!.length
        return true
      }
      if (sample.key === 'Enter') {
        this.#commit(citationStep(this.#options.diagram(), this.#cycle.candidate, this.#cycle.index))
        this.#cycle = null
        return true
      }
    }
    if ((sample.key === 'f' || sample.key === 'F')
      && !sample.ctrlKey && !sample.altKey && !sample.metaKey) {
      const selection = this.#options.selection()
      if (selection.length !== 1 || selection[0]?.kind !== 'wire') return false
      this.#commit({ rule: 'fusion', wire: selection[0].id })
      return true
    }
    if (sample.key !== 'Delete' && sample.key !== 'Backspace' && sample.key !== 'w' && sample.key !== 'W') return false
    const discovery = discoverProofActions(
      this.#options.diagram(),
      this.#options.selection(),
      this.#options.context(),
      this.#options.orientation(),
    )
    if (discovery === null) {
      this.#options.refuse(this.#options.selection().length === 0 ? 'select something first' : 'this selection spans several regions', this.#lastPointer)
      return true
    }
    if (sample.key === 'Delete' || sample.key === 'Backspace') {
      const step = contextualDeleteStep(this.#options.diagram(), discovery, this.#options.fuel())
      if (step === null) this.#options.refuse('nothing here reads as a deletion', this.#lastPointer)
      else this.#commit(step)
      return true
    }
    if (sample.shiftKey) {
      this.#options.openAbstraction(discovery.sel, this.#lastPointer)
      this.cancel()
    } else this.#commit({ rule: 'doubleCutIntro', sel: discovery.sel })
    return true
  }

  overlay(): readonly Shape[] {
    const out: Shape[] = [...this.#connection.overlay(), ...this.#fission.overlay(), ...this.#copy.overlay()]
    const cycle = this.#cycle
    if (cycle !== null && cycle.candidate.occurrences !== null) {
      const occurrence = cycle.candidate.occurrences[cycle.index]!
      for (const node of occurrence.nodeMap.values()) {
        const body = this.#options.engine().bodies.get(node)
        if (body !== undefined) out.push({ kind: 'circle', center: body.pos, r: body.discR * this.#options.engine().scale + 1.5, fill: null, stroke: '#7c3aed', width: 2.6, insetColor: null, glow: null })
      }
    }
    return out
  }

  cancel(): void {
    this.#closeMenu()
    this.#closePrompt()
    this.#cycle = null
    this.#connection.cancel()
    this.#fission.cancel()
    this.#copy.cancel()
  }

  dispose(): void { this.cancel(); this.#fission.dispose(); this.#copy.dispose() }

  passiveSample(sample: PointerSample | null): void { this.#fission.hover(this.#copy.dragging ? null : sample) }
  modifiersChanged(ctrlHeld: boolean): void { this.#fission.modifiersChanged(ctrlHeld); this.#copy.modifiersChanged(ctrlHeld) }

  #commit(step: ProofStep): void {
    try {
      this.#options.apply(singleStepAction(step.rule === 'theorem' ? `cite ${step.name}` : step.rule, step))
      this.#options.setSelection([])
      this.#closeMenu()
      this.#closePrompt()
    } catch (error) {
      this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer)
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
      if (run !== null) element.addEventListener('click', () => {
        try { run() } catch (error) { this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer) }
      })
      menu.append(element)
    }
    const d = this.#options.diagram()
    const region = regionAt(this.#options.engine(), d, sample.world)
    const discovery = discoverProofActions(d, hits, this.#options.context(), this.#options.orientation())
    if (discovery !== null) {
      row('Actions', null)
      for (const action of discovery.actions) this.#appendAction(row, action, discovery.sel)
    }
    const candidates = citationCandidates(d, hits, discovery?.sel.region ?? region, this.#options.context(), this.#options.orientation(), this.#options.fuel())
    const citations = hits.length === 0 ? { applicable: [], closed: candidates.closed } : candidates
    if (citations.applicable.length > 0) {
      row('Applicable theorems', null)
      for (const candidate of citations.applicable) row(`${candidate.name} (${candidate.occurrences!.length === 1 ? 'applies' : `${candidate.occurrences!.length} places`})`, () => this.#beginCitation(candidate))
    }
    if (citations.closed.length > 0) {
      row('Closed theorems', null)
      for (const candidate of citations.closed) row(candidate.name, () => this.#commit(citationStep(d, candidate, undefined, region)))
    }
    if (menu.childElementCount === 0) return
    this.#menu = menu
    this.#options.host.append(menu)
  }

  #appendAction(row: (label: string, run: (() => void) | null) => void, action: ActionDescriptor, sel: SubgraphSelection): void {
    switch (action.kind) {
      case 'erase': row(action.label, () => this.#commit(erasureStep(this.#options.diagram(), sel))); return
      case 'doubleCutWrap': row(action.label, () => this.#commit({ rule: 'doubleCutIntro', sel })); return
      case 'doubleCutElim': row(action.label, () => this.#commit({ rule: 'doubleCutElim', region: sel.regions[0]! })); return
      case 'abstractWrap': row(action.label, () => {
        this.#closeMenu()
        this.#options.openAbstraction(sel, this.#lastPointer)
      }); return
      case 'vacuousElim': row(action.label, () => this.#commit({ rule: 'vacuousElim', region: sel.regions[0]! })); return
      case 'iterate': row('Copy by dragging the selection', null); return
      case 'deiterate': row(action.label, () => this.#commit(
        deiterationStep(this.#options.diagram(), sel, this.#options.fuel()),
      )); return
      case 'convert': this.#appendConversions(row, sel.nodes[0]!); return
      case 'instantiate': {
        row('Instantiate with', null)
        const bubble = sel.regions[0]!
        const bubbleRegion = this.#options.diagram().regions[bubble]!
        const arity = bubbleRegion.kind === 'bubble' ? bubbleRegion.arity : -1
        for (const choice of instantiationChoices(this.#options.context(), arity)) {
          if (choice.kind === 'anonymous') row(choice.label, () => {
            this.#closeMenu()
            this.#options.openComprehension(bubble, this.#lastPointer)
          })
          else row(choice.label, () => this.#commit({ rule: 'comprehensionInstantiate', bubble, comp: foldedComprehension(this.#options.context(), choice.name), attachments: [], binders: {} }))
        }
        return
      }
      case 'relUnfold': row(action.label, () => this.#commit({ rule: 'relUnfold', node: sel.nodes[0]! })); return
      case 'relFold': {
        row('Fold into', null)
        for (const name of this.#options.context().relations.keys()) row(name, () => this.#commit({ rule: 'relFold', sel, defId: name, args: inferFoldArgs(this.#options.diagram(), sel, name, this.#options.context()) }))
        return
      }
      case 'citeTheorem': return
    }
  }

  #appendConversions(row: (label: string, run: (() => void) | null) => void, node: NodeId): void {
    row('Normalize (also: double-click)', () => this.doubleClick({ pointerId: 0, button: 0, client: this.#lastPointer, screen: this.#lastPointer, world: { x: 0, y: 0 }, hit: { kind: 'node', id: node }, shiftKey: false, ctrlKey: false, altKey: false, metaKey: false }))
    row('Convert → head normal', () => this.#commit(convertToHeadNormal(this.#options.diagram(), node, this.#options.fuel()).step))
    row('Convert → custom target…', () => this.#openTextPrompt('Conversion target', 'target term', (value) => {
      const term = parseTerm(value)
      const diagram = this.#options.diagram()
      const source = termNodeAt(diagram, node)
      const correspondence = proposePortCorrespondence(source.term, term, source.freePorts)
      const conversion = applyConversion(diagram, node, term, correspondence, this.#options.fuel())
      this.#commit({ rule: 'conversion', node, term, certificate: conversion.certificate, correspondence, attachments: {} })
    }))
  }

  #beginCitation(candidate: CitationCandidate): void {
    if (candidate.occurrences === null) return
    this.#closeMenu()
    if (candidate.occurrences.length === 1) {
      this.#commit(citationStep(this.#options.diagram(), candidate, 0))
      return
    }
    this.#cycle = { candidate, index: 0 }
  }

  #openTextPrompt(label: string, placeholder: string, accept: (value: string) => void): void {
    this.#closePrompt()
    const wrap = this.#document.createElement('div')
    wrap.className = 'vpa-proof-prompt'
    wrap.style.cssText = `position:fixed;left:${this.#lastPointer.x + 10}px;top:${this.#lastPointer.y + 10}px;z-index:32`
    const input = this.#document.createElement('input')
    input.setAttribute('aria-label', label)
    input.placeholder = placeholder
    input.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') this.#closePrompt()
      if (event.key !== 'Enter') return
      try { accept(input.value) } catch (error) { this.#options.refuse(error instanceof Error ? error.message : String(error), this.#lastPointer) }
    })
    wrap.append(input)
    this.#prompt = wrap
    this.#options.host.append(wrap)
    queueMicrotask(() => input.focus())
  }

  #closeMenu(): void { this.#menu?.remove(); this.#menu = null }
  #closePrompt(): void { this.#prompt?.remove(); this.#prompt = null }
}
