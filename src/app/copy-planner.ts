import { mkDiagram, portKey, type Diagram, type Endpoint, type NodeId, type RegionId, type Wire, type WireId } from '../kernel/diagram/diagram'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { boundaryForm, exploreForm } from '../kernel/diagram/canonical/explore'
import { diagramToJson } from '../kernel/diagram/json'
import { freshId } from '../kernel/diagram/subgraph/freshId'
import { extractSubgraph, type Extraction } from '../kernel/diagram/subgraph/extract'
import { spliceSubgraphMapped } from '../kernel/diagram/subgraph/splice'
import type { IdReservation } from '../kernel/diagram/subgraph/freshId'
import { mkSelection, selectionContents, type SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import {
  allocationReservation,
  applyAction,
  type ProofAction,
  type ProofAllocation,
} from '../kernel/proof/action'
import { dwbToJson, theoremToJson } from '../kernel/proof/json'
import { applyStep, type ProofStep } from '../kernel/proof/step'
import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext } from '../kernel/proof/context'
import { app, bvar, freePorts, lam, type Term } from '../kernel/term/term'
import type { PathSeg } from '../kernel/term/reduce'
import type { Vec2 } from '../view/vec'
import type { ProofOrientation } from './interact/moves'

export type CopyDestination =
  | { readonly kind: 'workspace'; readonly draft: Diagram; readonly region: RegionId; readonly at: Vec2 }
  | { readonly kind: 'edit'; readonly diagram: Diagram; readonly region: RegionId; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly diagram: Diagram; readonly region: RegionId; readonly orientation: ProofOrientation; readonly ctx: ProofContext }

export type CopyRefusalCode =
  | 'invalid-selection'
  | 'invalid-destination'
  | 'invalid-attachment'
  | 'external-binder'
  | 'unsupported-structure'
  | 'proof-unavailable'
  | 'fingerprint-mismatch'
  | 'stale-source'
  | 'stale-destination'
  | 'invalid-plan'

export type CopyRefusal = {
  readonly ok: false
  readonly kind: 'refusal'
  readonly code: CopyRefusalCode
  readonly message: string
}

type CopyEvidence = {
  readonly sourceState: string
  readonly destinationState: string
  readonly selection: SubgraphSelection
}

export type CopyPlan =
  | { readonly kind: 'workspace' | 'edit'; readonly result: Diagram; readonly introduced: readonly NodeId[]; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly action: ProofAction; readonly resultFingerprint: string }

/** Revalidation authority is deliberately ephemeral and bound to one in-process plan object. */
const planEvidence = new WeakMap<CopyPlan, CopyEvidence>()

type StructuralKind = 'workspace' | 'edit'

type Candidate = {
  readonly action: ProofAction
  readonly replayed: Diagram
}

type ConstructionRecipe = {
  readonly steps: readonly ProofStep[]
  readonly attachmentMap: ReadonlyMap<WireId, WireId>
}

type FissionEdge = {
  readonly wire: WireId
  readonly producer: NodeId
  readonly consumer: NodeId
  readonly inputName: string
  readonly path: readonly PathSeg[]
}

type FissionTree = {
  readonly root: NodeId
  readonly nodes: readonly NodeId[]
  readonly fusedTerm: Term
  readonly children: ReadonlyMap<NodeId, readonly FissionEdge[]>
}

type Compiler = {
  diagram: Diagram
  readonly steps: ProofStep[]
  readonly regionMap: Map<RegionId, RegionId>
  readonly nodeMap: Map<NodeId, NodeId>
  readonly wireMap: Map<WireId, WireId>
  readonly pattern: DiagramWithBoundary
  readonly destination: Extract<CopyDestination, { readonly kind: 'proof' }>
  readonly reservation: IdReservation
}

function deny(code: CopyRefusalCode, message: string): CopyRefusal {
  return Object.freeze({ ok: false as const, kind: 'refusal' as const, code, message })
}

function isRefusal(value: Candidate | ConstructionRecipe | CopyRefusal): value is CopyRefusal {
  return 'kind' in value && value.kind === 'refusal'
}

function canonicalSemanticJson(value: unknown, field?: string): unknown {
  if (value === null || typeof value !== 'object') return value
  if (Array.isArray(value)) {
    const values = value.map((entry) => canonicalSemanticJson(entry))
    if (field === 'endpoints') {
      values.sort((a, b) => compareCodeUnits(JSON.stringify(a), JSON.stringify(b)))
    }
    return values
  }
  const record = value as Readonly<Record<string, unknown>>
  return Object.fromEntries(Object.keys(record).sort().map((key) => [
    key,
    canonicalSemanticJson(record[key], key),
  ]))
}

function compareCodeUnits(a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function semanticJsonFingerprint(value: unknown): string {
  return JSON.stringify(canonicalSemanticJson(value))
}

function diagramStateFingerprint(diagram: Diagram): string {
  // diagramToJson is injective over exact region/node/wire ids, terms, ports,
  // scopes, and node ownership. Only endpoint-set iteration order is erased.
  return semanticJsonFingerprint(diagramToJson(diagram))
}

function contextState(ctx: ProofContext): unknown {
  return {
    relations: [...ctx.relations.entries()]
      .sort(([a], [b]) => compareCodeUnits(a, b))
      .map(([name, relation]) => [name, dwbToJson(relation)]),
    theorems: [...ctx.theorems.entries()]
      .sort(([a], [b]) => compareCodeUnits(a, b))
      .map(([name, theorem]) => [name, theoremToJson(theorem)]),
  }
}

function destinationDiagram(destination: CopyDestination): Diagram {
  return destination.kind === 'workspace' ? destination.draft : destination.diagram
}

function destinationState(destination: CopyDestination): string {
  switch (destination.kind) {
    case 'workspace':
      return semanticJsonFingerprint({
        kind: destination.kind,
        draft: diagramToJson(destination.draft),
        region: destination.region,
        at: { x: destination.at.x, y: destination.at.y },
      })
    case 'edit':
      return semanticJsonFingerprint({
        kind: destination.kind,
        diagram: diagramToJson(destination.diagram),
        region: destination.region,
        at: { x: destination.at.x, y: destination.at.y },
      })
    case 'proof':
      return semanticJsonFingerprint({
        kind: destination.kind,
        diagram: diagramToJson(destination.diagram),
        region: destination.region,
        orientation: destination.orientation,
        ctx: contextState(destination.ctx),
      })
  }
}

function finishPlan(
  value: CopyPlan,
  source: Diagram,
  selection: SubgraphSelection,
  destination: CopyDestination,
): CopyPlan {
  const evidence: CopyEvidence = Object.freeze({
    sourceState: diagramStateFingerprint(source),
    destinationState: destinationState(destination),
    selection: mkSelection(source, selection),
  })
  const finished = Object.freeze(value)
  planEvidence.set(finished, evidence)
  return finished
}

function classifyStructuralError(error: unknown): CopyRefusal {
  const message = error instanceof Error ? error.message : String(error)
  if (/attachment wire|expected .* attachments|does not enclose splice region/.test(message)) {
    return deny('invalid-attachment', message)
  }
  if (/region|coordinates/.test(message)) return deny('invalid-destination', message)
  return deny('invalid-selection', message)
}

function validateDestination(destination: CopyDestination): CopyRefusal | null {
  if (destination.kind === 'proof') assertProofContext(destination.ctx)
  const diagram = destinationDiagram(destination)
  if (diagram.regions[destination.region] === undefined) {
    return deny('invalid-destination', `copy destination region '${destination.region}' does not exist`)
  }
  if (destination.kind !== 'proof' && (!Number.isFinite(destination.at.x) || !Number.isFinite(destination.at.y))) {
    return deny('invalid-destination', 'copy destination coordinates must be finite')
  }
  return null
}

function sourceAllocation(source: Diagram): ProofAllocation {
  return Object.freeze({
    regions: Object.freeze(Object.keys(source.regions).sort()),
    nodes: Object.freeze(Object.keys(source.nodes).sort()),
    wires: Object.freeze(Object.keys(source.wires).sort()),
  })
}

function planStructural(
  kind: StructuralKind,
  source: Diagram,
  selection: SubgraphSelection,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: StructuralKind }>,
): CopyPlan | CopyRefusal {
  const host = destination.kind === 'workspace' ? destination.draft : destination.diagram
  const pattern = extraction.pattern
  const reserved = allocationReservation(sourceAllocation(source))
  try {
    let mapped: ReturnType<typeof spliceSubgraphMapped>
    if (destination.kind === 'edit') {
      mapped = spliceSubgraphMapped(host, destination.region, pattern, extraction.attachments, { reserved })
    } else {
      const taken = new Set([
        ...Object.keys(source.wires),
        ...Object.keys(host.wires),
        ...Object.keys(pattern.diagram.wires),
      ])
      const representative = new Map<WireId, WireId>()
      const wires: Record<WireId, Wire> = { ...host.wires }
      const loose = pattern.boundary.map((stub, index) => {
        const prior = representative.get(stub)
        if (prior !== undefined) return prior
        const wire = freshId(taken, `copy_boundary_${extraction.attachments[index] ?? index}`)
        taken.add(wire)
        representative.set(stub, wire)
        wires[wire] = { scope: host.root, endpoints: [] }
        return wire
      })
      const seeded = mkDiagram({ root: host.root, regions: { ...host.regions }, nodes: { ...host.nodes }, wires })
      mapped = spliceSubgraphMapped(seeded, destination.region, pattern, loose, { reserved })
    }
    return finishPlan({
      kind,
      result: mapped.diagram,
      introduced: Object.freeze([...mapped.nodeMap.values()].sort()),
      at: Object.freeze({ x: destination.at.x, y: destination.at.y }),
    }, source, selection, destination)
  } catch (error) {
    return classifyStructuralError(error)
  }
}

function introducedCopySelection(before: Diagram, after: Diagram, region: RegionId): SubgraphSelection {
  const allNewNodes = new Set(Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined))
  const regions = Object.keys(after.regions).filter((id) => {
    const value = after.regions[id]!
    return before.regions[id] === undefined && value.kind !== 'sheet' && value.parent === region
  })
  const nodes = [...allNewNodes].filter((id) => after.nodes[id]!.region === region)
  const wires = Object.keys(after.wires).filter((id) => {
    const wire = after.wires[id]!
    return before.wires[id] === undefined
      && wire.scope === region
      && wire.endpoints.every((endpoint) => allNewNodes.has(endpoint.node))
  })
  return mkSelection(after, { region, regions, nodes, wires })
}

function frozenAction(steps: readonly ProofStep[], allocation: ProofAllocation): ProofAction {
  return Object.freeze({
    label: 'Copy selection',
    steps: Object.freeze([...steps]),
    placements: Object.freeze([]),
    allocation,
  })
}

function verifyCandidate(
  before: Diagram,
  intended: Diagram,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
  steps: readonly ProofStep[],
  allocation: ProofAllocation,
): Candidate | CopyRefusal {
  const action = frozenAction(steps, allocation)
  let replayed: Diagram
  try {
    replayed = applyAction(before, action, destination.ctx, destination.orientation)
  } catch (error) {
    return deny('proof-unavailable', error instanceof Error ? error.message : String(error))
  }
  if (exploreForm(replayed) !== exploreForm(intended)) {
    return deny('fingerprint-mismatch', 'scratch replay did not construct the exact intended diagram')
  }
  try {
    const alleged = extractSubgraph(replayed, introducedCopySelection(before, replayed, destination.region))
    if (boundaryForm(alleged.pattern) !== boundaryForm(extraction.pattern)) {
      return deny('fingerprint-mismatch', 'scratch replay copy does not match the boundary-pinned source pattern')
    }
    if (JSON.stringify(alleged.attachments) !== JSON.stringify(extraction.attachments)) {
      return deny('fingerprint-mismatch', 'scratch replay changed a crossing attachment identity')
    }
    return { action, replayed }
  } catch (error) {
    return deny('fingerprint-mismatch', error instanceof Error ? error.message : String(error))
  }
}

function childRegions(diagram: Diagram, parent: RegionId): readonly RegionId[] {
  return Object.entries(diagram.regions)
    .filter(([, region]) => region.kind !== 'sheet' && region.parent === parent)
    .map(([id]) => id)
    .sort()
}

function pairedCutChoice(diagram: Diagram, outer: RegionId, memo: Map<RegionId, RegionId | null>): RegionId | null {
  const cached = memo.get(outer)
  if (cached !== undefined) return cached
  const children = childRegions(diagram, outer)
  const candidates = children.filter((id) => diagram.regions[id]!.kind === 'cut')
  for (const inner of candidates) {
    let valid = true
    for (const child of children) {
      if (child === inner) {
        valid = regionChildrenConstructible(diagram, child, memo)
      } else {
        valid = regionRootConstructible(diagram, child, memo)
      }
      if (!valid) break
    }
    if (valid) {
      memo.set(outer, inner)
      return inner
    }
  }
  memo.set(outer, null)
  return null
}

function regionRootConstructible(diagram: Diagram, region: RegionId, memo: Map<RegionId, RegionId | null>): boolean {
  const value = diagram.regions[region]!
  return value.kind === 'bubble'
    ? regionChildrenConstructible(diagram, region, memo)
    : value.kind === 'cut' && pairedCutChoice(diagram, region, memo) !== null
}

function regionChildrenConstructible(diagram: Diagram, parent: RegionId, memo: Map<RegionId, RegionId | null>): boolean {
  return childRegions(diagram, parent).every((child) => regionRootConstructible(diagram, child, memo))
}

function emit(compiler: Compiler, step: ProofStep): { readonly regions: readonly RegionId[]; readonly nodes: readonly NodeId[] } {
  const before = compiler.diagram
  compiler.diagram = applyStep(
    before,
    step,
    compiler.destination.ctx,
    compiler.destination.orientation,
    compiler.reservation,
  )
  compiler.steps.push(step)
  return {
    regions: Object.freeze(Object.keys(compiler.diagram.regions).filter((id) => before.regions[id] === undefined).sort()),
    nodes: Object.freeze(Object.keys(compiler.diagram.nodes).filter((id) => before.nodes[id] === undefined).sort()),
  }
}

function emptySelection(diagram: Diagram, region: RegionId): SubgraphSelection {
  return mkSelection(diagram, { region, regions: [], nodes: [], wires: [] })
}

function compileRegionRoot(
  compiler: Compiler,
  patternRegion: RegionId,
  destinationParent: RegionId,
  pairing: Map<RegionId, RegionId | null>,
): void {
  const value = compiler.pattern.diagram.regions[patternRegion]!
  if (value.kind === 'bubble') {
    const made = emit(compiler, { rule: 'vacuousIntro', sel: emptySelection(compiler.diagram, destinationParent), arity: value.arity })
    if (made.regions.length !== 1) throw new Error('vacuous introduction did not create exactly one bubble')
    const destinationRegion = made.regions[0]!
    compiler.regionMap.set(patternRegion, destinationRegion)
    compileRegionChildren(compiler, patternRegion, destinationRegion, pairing)
    return
  }
  if (value.kind !== 'cut') throw new Error('the extracted pattern root cannot be compiled as content')
  const inner = pairedCutChoice(compiler.pattern.diagram, patternRegion, pairing)
  if (inner === null) throw new Error(`cut '${patternRegion}' has no complete parent-child double-cut pairing`)
  const made = emit(compiler, { rule: 'doubleCutIntro', sel: emptySelection(compiler.diagram, destinationParent) })
  if (made.regions.length !== 2) throw new Error('double-cut introduction did not create exactly two cuts')
  const outerDestination = made.regions.find((id) => {
    const region = compiler.diagram.regions[id]!
    return region.kind === 'cut' && region.parent === destinationParent
  })
  if (outerDestination === undefined) throw new Error('double-cut introduction did not create its outer cut')
  const innerDestination = made.regions.find((id) => id !== outerDestination)
  if (innerDestination === undefined) throw new Error('double-cut introduction did not create its inner cut')
  compiler.regionMap.set(patternRegion, outerDestination)
  compiler.regionMap.set(inner, innerDestination)
  for (const child of childRegions(compiler.pattern.diagram, patternRegion)) {
    if (child !== inner) compileRegionRoot(compiler, child, outerDestination, pairing)
  }
  compileRegionChildren(compiler, inner, innerDestination, pairing)
}

function compileRegionChildren(
  compiler: Compiler,
  patternParent: RegionId,
  destinationParent: RegionId,
  pairing: Map<RegionId, RegionId | null>,
): void {
  for (const child of childRegions(compiler.pattern.diagram, patternParent)) {
    compileRegionRoot(compiler, child, destinationParent, pairing)
  }
}

function endpointWire(diagram: Diagram, endpoint: Endpoint): WireId {
  const key = portKey(endpoint.port)
  const found = Object.entries(diagram.wires).find(([, wire]) =>
    wire.endpoints.some((candidate) => candidate.node === endpoint.node && portKey(candidate.port) === key),
  )
  if (found === undefined) throw new Error(`constructed port '${key}' of node '${endpoint.node}' has no wire`)
  return found[0]
}

function emitTermNode(compiler: Compiler, region: RegionId, term: Term): NodeId {
  const made = emit(compiler, freePorts(term).length === 0
    ? { rule: 'closedTermIntro', region, term }
    : { rule: 'openTermSpawn', region, term })
  if (made.nodes.length !== 1) throw new Error('term constructor did not create exactly one node')
  return made.nodes[0]!
}

function emitFissionTree(compiler: Compiler, tree: FissionTree): void {
  const pd = compiler.pattern.diagram
  const sourceRoot = pd.nodes[tree.root]
  if (sourceRoot?.kind !== 'term') throw new Error('fission tree root is not a term')
  const region = compiler.regionMap.get(sourceRoot.region)
  if (region === undefined) throw new Error(`pattern region '${sourceRoot.region}' was not constructed`)
  const replayRoot = emitTermNode(compiler, region, tree.fusedTerm)
  compiler.nodeMap.set(tree.root, replayRoot)

  const splitChildren = (sourceConsumer: NodeId, replayConsumer: NodeId): void => {
    for (const edge of tree.children.get(sourceConsumer) ?? []) {
      const current = compiler.diagram.nodes[replayConsumer]
      if (current?.kind !== 'term') throw new Error(`fission replay node '${replayConsumer}' is not a term`)
      const beforeWires = new Set(Object.keys(compiler.diagram.wires))
      const split = emit(compiler, { rule: 'fission', node: replayConsumer, path: edge.path })
      if (split.nodes.length !== 1) throw new Error('fission tree edge did not create exactly one producer')
      const madeWires = Object.keys(compiler.diagram.wires).filter((wire) => !beforeWires.has(wire))
      if (madeWires.length !== 1) throw new Error('fission tree edge did not create exactly one bridge wire')
      const replayProducer = split.nodes[0]!
      compiler.nodeMap.set(edge.producer, replayProducer)
      compiler.wireMap.set(edge.wire, madeWires[0]!)
      splitChildren(edge.producer, replayProducer)
    }
  }
  splitChildren(tree.root, replayRoot)
}

function compileNodes(compiler: Compiler, fissions: readonly FissionTree[]): void {
  const pd = compiler.pattern.diagram
  const treeByNode = new Map<NodeId, FissionTree>()
  for (const tree of fissions) {
    for (const node of tree.nodes) {
      if (treeByNode.has(node)) throw new Error('fission trees must have disjoint node ownership')
      treeByNode.set(node, tree)
    }
  }
  const emitted = new Set<FissionTree>()
  for (const id of Object.keys(pd.nodes).sort()) {
    const tree = treeByNode.get(id)
    if (tree !== undefined) {
      if (!emitted.has(tree)) {
        emitFissionTree(compiler, tree)
        emitted.add(tree)
      }
      continue
    }
    const node = pd.nodes[id]!
    const region = compiler.regionMap.get(node.region)
    if (region === undefined) throw new Error(`pattern region '${node.region}' was not constructed`)
    let made: { readonly nodes: readonly NodeId[] }
    switch (node.kind) {
      case 'term':
        made = { nodes: [emitTermNode(compiler, region, node.term)] }
        break
      case 'ref':
        made = emit(compiler, { rule: 'relationSpawn', region, defId: node.defId, arity: node.arity })
        break
      case 'atom': {
        const binder = compiler.regionMap.get(node.binder)
        if (binder === undefined) throw new Error(`bound relation references unconstructed binder '${node.binder}'`)
        const value = pd.regions[node.binder]
        if (value === undefined || value.kind !== 'bubble') throw new Error(`bound relation binder '${node.binder}' is not a bubble`)
        made = emit(compiler, { rule: 'boundRelationSpawn', region, binder, arity: value.arity })
        break
      }
    }
    if (made.nodes.length !== 1) throw new Error(`atomic constructor for '${id}' did not create exactly one node`)
    compiler.nodeMap.set(id, made.nodes[0]!)
  }
}

function mappedEndpoint(compiler: Compiler, endpoint: Endpoint): Endpoint {
  const node = compiler.nodeMap.get(endpoint.node)
  if (node === undefined) throw new Error(`pattern node '${endpoint.node}' was not constructed`)
  return { node, port: endpoint.port }
}

function joinInto(compiler: Compiler, survivor: WireId, other: WireId): WireId {
  if (survivor === other) return survivor
  const before = compiler.diagram
  const survivorScope = before.wires[survivor]?.scope
  const otherScope = before.wires[other]?.scope
  emit(compiler, { rule: 'wireJoin', a: survivor, b: other })
  if (compiler.diagram.wires[survivor] !== undefined) return survivor
  if (compiler.diagram.wires[other] !== undefined) return other
  throw new Error(
    `wire join removed both candidate identities '${survivor}' (${survivorScope}) and '${other}' (${otherScope})`,
  )
}

function constructLooseWire(compiler: Compiler, scope: RegionId, label: WireId): WireId {
  const witness = emit(compiler, { rule: 'closedTermIntro', region: scope, term: lam(bvar(0)) })
  if (witness.nodes.length !== 1) throw new Error(`empty-wire witness for '${label}' did not create exactly one node`)
  const wire = endpointWire(compiler.diagram, { node: witness.nodes[0]!, port: { kind: 'output' } })
  emit(compiler, {
    rule: 'erasure',
    sel: mkSelection(compiler.diagram, { region: scope, regions: [], nodes: [witness.nodes[0]!], wires: [] }),
  })
  const loose = compiler.diagram.wires[wire]
  if (loose === undefined || loose.scope !== scope || loose.endpoints.length !== 0) {
    throw new Error(`empty-wire witness for '${label}' did not leave one loose wire at '${scope}'`)
  }
  return wire
}

function compileWires(compiler: Compiler, extraction: Extraction): ReadonlyMap<WireId, WireId> {
  const pd = compiler.pattern.diagram
  const attachmentOf = new Map<WireId, WireId>()
  compiler.pattern.boundary.forEach((stub, index) => attachmentOf.set(stub, extraction.attachments[index]!))
  const explicitAttachments = new Map<WireId, WireId>()
  for (const wireId of Object.keys(pd.wires).sort()) {
    const wire = pd.wires[wireId]!
    if (compiler.wireMap.has(wireId)) continue
    if (wire.endpoints.length === 0) {
      const scope = compiler.regionMap.get(wire.scope)
      if (scope === undefined) throw new Error(`wire scope '${wire.scope}' was not constructed`)
      constructLooseWire(compiler, scope, wireId)
      continue
    }
    const endpoints = wire.endpoints.map((endpoint) => mappedEndpoint(compiler, endpoint))
    const attachment = attachmentOf.get(wireId)
    let survivor: WireId
    if (attachment !== undefined) {
      if (compiler.diagram.wires[attachment] === undefined) throw new Error(`attachment wire '${attachment}' does not exist`)
      survivor = attachment
      explicitAttachments.set(attachment, survivor)
    } else {
      const scope = compiler.regionMap.get(wire.scope)
      if (scope === undefined) throw new Error(`wire scope '${wire.scope}' was not constructed`)
      const exact = endpoints.find((endpoint) => compiler.diagram.nodes[endpoint.node]!.region === scope)
      survivor = exact === undefined
        ? constructLooseWire(compiler, scope, wireId)
        : endpointWire(compiler.diagram, exact)
    }
    for (const endpoint of endpoints) survivor = joinInto(compiler, survivor, endpointWire(compiler.diagram, endpoint))
  }
  return new Map(explicitAttachments)
}

function compileConstruction(
  before: Diagram,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
  reservation: IdReservation,
  fissions: readonly FissionTree[] = [],
): ConstructionRecipe | CopyRefusal {
  const pairing = new Map<RegionId, RegionId | null>()
  if (!regionChildrenConstructible(extraction.pattern.diagram, extraction.pattern.diagram.root, pairing)) {
    return deny('unsupported-structure', 'selected cut structure cannot be produced by complete parent-child double-cut introductions')
  }
  const compiler: Compiler = {
    diagram: before,
    steps: [],
    regionMap: new Map([[extraction.pattern.diagram.root, destination.region]]),
    nodeMap: new Map(),
    wireMap: new Map(),
    pattern: extraction.pattern,
    destination,
    reservation,
  }
  try {
    compileRegionChildren(compiler, extraction.pattern.diagram.root, destination.region, pairing)
    compileNodes(compiler, fissions)
    const attachments = compileWires(compiler, extraction)
    if (attachments.size !== new Set(extraction.attachments).size) {
      return deny('invalid-attachment', 'ordinary construction did not preserve every crossing attachment identity')
    }
    if (compiler.steps.length === 0) {
      return deny('unsupported-structure', 'the selected pattern has no constructible content')
    }
    return Object.freeze({
      steps: Object.freeze([...compiler.steps]),
      attachmentMap: attachments,
    })
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error)
    if (/attachment wire/.test(message)) return deny('invalid-attachment', message)
    if (/double-cut pairing|requires scope|unconstructed binder/.test(message)) {
      return deny('unsupported-structure', message)
    }
    return deny('proof-unavailable', message)
  }
}

function completeAttachmentMap(recipe: ConstructionRecipe, extraction: Extraction): boolean {
  const expected = new Set(extraction.attachments)
  return recipe.attachmentMap.size === expected.size
    && [...expected].every((attachment) => recipe.attachmentMap.get(attachment) === attachment)
}

/** Exact whole-pattern contextual constructor: spawn a matching named relation, pin its arguments, then unfold it. */
function compileContextualRelation(
  before: Diagram,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
  reservation: IdReservation,
): ConstructionRecipe | null {
  const targetForm = boundaryForm(extraction.pattern)
  const matches = [...destination.ctx.relations.entries()]
    .filter(([, relation]) => boundaryForm(relation) === targetForm)
    .sort(([a], [b]) => compareCodeUnits(a, b))
  for (const [defId, relation] of matches) {
    const compiler: Compiler = {
      diagram: before,
      steps: [],
      regionMap: new Map([[extraction.pattern.diagram.root, destination.region]]),
      nodeMap: new Map(),
      wireMap: new Map(),
      pattern: extraction.pattern,
      destination,
      reservation,
    }
    try {
      const made = emit(compiler, {
        rule: 'relationSpawn', region: destination.region, defId, arity: relation.boundary.length,
      })
      if (made.nodes.length !== 1) throw new Error(`contextual relation '${defId}' did not create exactly one reference`)
      const reference = made.nodes[0]!
      const attachmentMap = new Map<WireId, WireId>()
      for (let index = 0; index < extraction.attachments.length; index++) {
        const attachment = extraction.attachments[index]!
        const argument = endpointWire(compiler.diagram, {
          node: reference,
          port: { kind: 'arg', index },
        })
        const survivor = joinInto(compiler, attachment, argument)
        if (survivor !== attachment) throw new Error(`contextual relation changed attachment '${attachment}'`)
        attachmentMap.set(attachment, survivor)
      }
      emit(compiler, { rule: 'relUnfold', node: reference })
      return Object.freeze({
        steps: Object.freeze([...compiler.steps]),
        attachmentMap: new Map(attachmentMap),
      })
    } catch {
      // Another exact contextual constructor or the structural grammar may
      // still pass its real gates. Failed scratch state remains local.
    }
  }
  return null
}

function portOccurrencePaths(term: Term, name: string): readonly (readonly PathSeg[])[] {
  const paths: PathSeg[][] = []
  const visit = (current: Term, path: PathSeg[]): void => {
    switch (current.kind) {
      case 'lam': visit(current.body, [...path, 'body']); return
      case 'app':
        visit(current.fn, [...path, 'fn'])
        visit(current.arg, [...path, 'arg'])
        return
      case 'port':
        if (current.name === name) paths.push([...path])
        return
      case 'bvar':
        return
    }
  }
  visit(term, [])
  return paths
}

function substituteChildTerms(term: Term, children: ReadonlyMap<string, Term>): Term {
  switch (term.kind) {
    case 'bvar': return term
    case 'port': return children.get(term.name) ?? term
    case 'lam': return lam(substituteChildTerms(term.body, children))
    case 'app': return app(substituteChildTerms(term.fn, children), substituteChildTerms(term.arg, children))
  }
}

/** Discover the deterministic acyclic forest of exact internal fusion edges. */
function fissionTrees(extraction: Extraction): readonly FissionTree[] {
  const pd = extraction.pattern.diagram
  const edges: FissionEdge[] = []
  for (const [bridgeId, bridge] of Object.entries(pd.wires).sort(([a], [b]) => compareCodeUnits(a, b))) {
    if (extraction.pattern.boundary.includes(bridgeId) || bridge.endpoints.length !== 2) continue
    const output = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'output')
    const input = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'freeVar')
    if (output === undefined || input === undefined || output.node === input.node || input.port.kind !== 'freeVar') continue
    const producer = pd.nodes[output.node]
    const consumer = pd.nodes[input.node]
    if (producer?.kind !== 'term' || consumer?.kind !== 'term') continue
    if (producer.region !== consumer.region || bridge.scope !== producer.region) continue
    const paths = portOccurrencePaths(consumer.term, input.port.name)
    if (paths.length !== 1) continue
    edges.push(Object.freeze({
      wire: bridgeId,
      producer: output.node,
      consumer: input.node,
      inputName: input.port.name,
      path: Object.freeze([...paths[0]!]),
    }))
  }
  if (edges.length === 0) return []

  const outgoing = new Map<NodeId, FissionEdge>()
  const children = new Map<NodeId, FissionEdge[]>()
  const adjacency = new Map<NodeId, Set<NodeId>>()
  const invalid = new Set<NodeId>()
  for (const edge of edges) {
    if (outgoing.has(edge.producer)) {
      invalid.add(edge.producer)
      invalid.add(edge.consumer)
    } else {
      outgoing.set(edge.producer, edge)
    }
    const prior = children.get(edge.consumer) ?? []
    prior.push(edge)
    children.set(edge.consumer, prior)
    const producerLinks = adjacency.get(edge.producer) ?? new Set<NodeId>()
    producerLinks.add(edge.consumer)
    adjacency.set(edge.producer, producerLinks)
    const consumerLinks = adjacency.get(edge.consumer) ?? new Set<NodeId>()
    consumerLinks.add(edge.producer)
    adjacency.set(edge.consumer, consumerLinks)
  }
  const trees: FissionTree[] = []
  const visited = new Set<NodeId>()
  for (const start of [...adjacency.keys()].sort()) {
    if (visited.has(start)) continue
    const pending = [start]
    const component: NodeId[] = []
    while (pending.length > 0) {
      const node = pending.pop()!
      if (visited.has(node)) continue
      visited.add(node)
      component.push(node)
      for (const adjacent of [...(adjacency.get(node) ?? [])].sort().reverse()) pending.push(adjacent)
    }
    component.sort()
    const owned = new Set(component)
    const componentEdges = edges.filter((edge) => owned.has(edge.producer) && owned.has(edge.consumer))
    const roots = component.filter((node) => !componentEdges.some((edge) => edge.producer === node))
    if (roots.length !== 1 || componentEdges.length !== component.length - 1) continue
    if (component.some((node) => invalid.has(node))) continue
    const root = roots[0]!
    const fused = new Map<NodeId, Term>()
    const visiting = new Set<NodeId>()
    const fuse = (nodeId: NodeId): Term => {
      const prior = fused.get(nodeId)
      if (prior !== undefined) return prior
      if (visiting.has(nodeId)) throw new Error('cyclic fission component')
      visiting.add(nodeId)
      const node = pd.nodes[nodeId]
      if (node?.kind !== 'term') throw new Error('fission tree contains a non-term node')
      const replacements = new Map<string, Term>()
      for (const edge of children.get(nodeId) ?? []) {
        if (!owned.has(edge.producer)) continue
        if (replacements.has(edge.inputName)) throw new Error('competing fission inputs')
        replacements.set(edge.inputName, fuse(edge.producer))
      }
      const result = substituteChildTerms(node.term, replacements)
      visiting.delete(nodeId)
      fused.set(nodeId, result)
      return result
    }
    try {
      const fusedTerm = fuse(root)
      if (fused.size !== component.length) continue
      if (freePorts(fusedTerm).length > 0) continue
      trees.push(Object.freeze({
        root,
        nodes: Object.freeze(component),
        fusedTerm,
        children: new Map(component.map((node) => [
          node,
          Object.freeze((children.get(node) ?? []).filter((edge) => owned.has(edge.producer))),
        ])),
      }))
    } catch {
      // Cyclic and competing ownership shapes are not finite fission trees.
    }
  }
  return Object.freeze(trees)
}

function acceptedProofPlan(
  source: Diagram,
  selection: SubgraphSelection,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
  candidate: Candidate,
): CopyPlan {
  return finishPlan({
    kind: 'proof',
    action: candidate.action,
    resultFingerprint: exploreForm(candidate.replayed),
  }, source, selection, destination)
}

function planProof(
  source: Diagram,
  selection: SubgraphSelection,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
): CopyPlan | CopyRefusal {
  const allocation = sourceAllocation(source)
  const reservation = allocationReservation(allocation)
  let intended: Diagram
  try {
    intended = spliceSubgraphMapped(
      destination.diagram,
      destination.region,
      extraction.pattern,
      extraction.attachments,
      { reserved: reservation },
    ).diagram
  } catch (error) {
    const classified = classifyStructuralError(error)
    return classified.code === 'invalid-destination' ? classified : deny('invalid-attachment', classified.message)
  }

  const iteration: ProofStep = { rule: 'iteration', sel: selection, target: destination.region }
  const iterated = verifyCandidate(destination.diagram, intended, extraction, destination, [iteration], allocation)
  if (!isRefusal(iterated)) {
    return acceptedProofPlan(source, selection, destination, iterated)
  }

  const contextual = compileContextualRelation(destination.diagram, extraction, destination, reservation)
  if (contextual !== null && completeAttachmentMap(contextual, extraction)) {
    const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, contextual.steps, allocation)
    if (!isRefusal(constructed)) return acceptedProofPlan(source, selection, destination, constructed)
  }

  const trees = fissionTrees(extraction)
  if (trees.length > 0) {
    const recipe = compileConstruction(destination.diagram, extraction, destination, reservation, trees)
    if (!isRefusal(recipe) && completeAttachmentMap(recipe, extraction)) {
      const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, recipe.steps, allocation)
      if (!isRefusal(constructed)) return acceptedProofPlan(source, selection, destination, constructed)
    }
  }

  const recipe = compileConstruction(destination.diagram, extraction, destination, reservation)
  if (isRefusal(recipe)) return recipe
  if (!completeAttachmentMap(recipe, extraction)) {
    return deny('invalid-attachment', 'ordinary construction did not preserve every crossing attachment identity')
  }
  const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, recipe.steps, allocation)
  if (isRefusal(constructed)) return constructed
  return acceptedProofPlan(source, selection, destination, constructed)
}

export function planCopy(
  source: Diagram,
  selection: SubgraphSelection,
  destination: CopyDestination,
): CopyPlan | CopyRefusal {
  const invalidDestination = validateDestination(destination)
  if (invalidDestination !== null) return invalidDestination
  let extraction: Extraction
  try {
    const contents = selectionContents(source, selection)
    if (contents.allRegions.size === 0 && contents.allNodes.size === 0 && contents.internalWires.length === 0) {
      return deny('invalid-selection', 'cannot copy an empty selection')
    }
    extraction = extractSubgraph(source, selection)
  } catch (error) {
    return deny('invalid-selection', error instanceof Error ? error.message : String(error))
  }
  if (extraction.binderStubs.length > 0) {
    return deny(
      'external-binder',
      `selection leaves ${extraction.binderStubs.length} external binder stub(s); include every binder in the copied pattern`,
    )
  }
  switch (destination.kind) {
    case 'workspace': return planStructural('workspace', source, selection, extraction, destination)
    case 'edit': return planStructural('edit', source, selection, extraction, destination)
    case 'proof': return planProof(source, selection, extraction, destination)
  }
}

export function revalidateCopy(
  plan: CopyPlan,
  liveSource: Diagram,
  liveDestination: CopyDestination,
): CopyPlan | CopyRefusal {
  const evidence = planEvidence.get(plan)
  if (evidence === undefined) return deny('invalid-plan', 'copy plan has no revalidation evidence')
  if (diagramStateFingerprint(liveSource) !== evidence.sourceState) {
    return deny('stale-source', 'copy source changed after the plan was created')
  }
  let liveDestinationState: string
  try {
    liveDestinationState = destinationState(liveDestination)
  } catch (error) {
    return deny('stale-destination', error instanceof Error ? error.message : String(error))
  }
  if (liveDestinationState !== evidence.destinationState) {
    return deny('stale-destination', 'copy destination changed after the plan was created')
  }
  return planCopy(liveSource, evidence.selection, liveDestination)
}
