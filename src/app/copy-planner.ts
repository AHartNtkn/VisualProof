import { mkDiagram, portKey, type Diagram, type DiagramNode, type Endpoint, type NodeId, type Region, type RegionId, type Wire, type WireId } from '../kernel/diagram/diagram'
import { mkDiagramWithBoundary, type DiagramWithBoundary } from '../kernel/diagram/boundary'
import { boundaryForm, exploreForm } from '../kernel/diagram/canonical/explore'
import { freshId } from '../kernel/diagram/subgraph/freshId'
import { extractSubgraph, type Extraction } from '../kernel/diagram/subgraph/extract'
import { spliceSubgraph } from '../kernel/diagram/subgraph/splice'
import { mkSelection, selectionContents, type SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { applyAction, type ProofAction } from '../kernel/proof/action'
import { applyStep, type ProofContext, type ProofStep } from '../kernel/proof/step'
import { bvar, freePorts, lam } from '../kernel/term/term'
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

const evidenceKey: unique symbol = Symbol('CopyPlanner evidence')
type EvidenceBacked = { readonly [evidenceKey]: CopyEvidence }

export type CopyPlan = (
  | { readonly kind: 'workspace' | 'edit'; readonly result: Diagram; readonly introduced: readonly NodeId[]; readonly at: Vec2 }
  | { readonly kind: 'proof'; readonly action: ProofAction; readonly resultFingerprint: string }
) & EvidenceBacked

type StructuralKind = 'workspace' | 'edit'

type Candidate = {
  readonly action: ProofAction
  readonly replayed: Diagram
}

type ConstructionRecipe = {
  readonly steps: readonly ProofStep[]
  readonly attachmentMap: ReadonlyMap<WireId, WireId>
}

type Compiler = {
  diagram: Diagram
  readonly steps: ProofStep[]
  readonly regionMap: Map<RegionId, RegionId>
  readonly nodeMap: Map<NodeId, NodeId>
  readonly pattern: DiagramWithBoundary
  readonly destination: Extract<CopyDestination, { readonly kind: 'proof' }>
}

function deny(code: CopyRefusalCode, message: string): CopyRefusal {
  return Object.freeze({ ok: false as const, kind: 'refusal' as const, code, message })
}

function isRefusal(value: Candidate | ConstructionRecipe | CopyRefusal): value is CopyRefusal {
  return 'kind' in value && value.kind === 'refusal'
}

function stableValue(value: unknown, seen = new Set<object>()): unknown {
  if (value === null || typeof value !== 'object') return value
  if (seen.has(value)) throw new Error('copy evidence cannot contain a cycle')
  seen.add(value)
  let normalized: unknown
  if (Array.isArray(value)) {
    normalized = value.map((entry) => stableValue(entry, seen))
  } else if (value instanceof Map) {
    const entries = [...value.entries()].map(([key, entry]) => [stableValue(key, seen), stableValue(entry, seen)] as const)
    entries.sort(([a], [b]) => compareCodeUnits(JSON.stringify(a), JSON.stringify(b)))
    normalized = { map: entries }
  } else if (value instanceof Set) {
    const entries = [...value].map((entry) => stableValue(entry, seen))
    entries.sort((a, b) => compareCodeUnits(JSON.stringify(a), JSON.stringify(b)))
    normalized = { set: entries }
  } else {
    const record = value as Readonly<Record<string, unknown>>
    normalized = Object.fromEntries(Object.keys(record).sort().map((key) => [key, stableValue(record[key], seen)]))
  }
  seen.delete(value)
  return normalized
}

function compareCodeUnits(a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function stateKey(value: unknown): string {
  return JSON.stringify(stableValue(value))
}

function destinationDiagram(destination: CopyDestination): Diagram {
  return destination.kind === 'workspace' ? destination.draft : destination.diagram
}

function destinationState(destination: CopyDestination): string {
  switch (destination.kind) {
    case 'workspace':
      return stateKey({ kind: destination.kind, draft: destination.draft, region: destination.region, at: destination.at })
    case 'edit':
      return stateKey({ kind: destination.kind, diagram: destination.diagram, region: destination.region, at: destination.at })
    case 'proof':
      return stateKey({
        kind: destination.kind,
        diagram: destination.diagram,
        region: destination.region,
        orientation: destination.orientation,
        ctx: destination.ctx,
      })
  }
}

function finishPlan<T extends Omit<CopyPlan, keyof EvidenceBacked>>(
  value: T,
  source: Diagram,
  selection: SubgraphSelection,
  destination: CopyDestination,
): CopyPlan {
  const evidence: CopyEvidence = Object.freeze({
    sourceState: stateKey(source),
    destinationState: destinationState(destination),
    selection: mkSelection(source, selection),
  })
  Object.defineProperty(value, evidenceKey, { value: evidence, enumerable: false, writable: false })
  return Object.freeze(value) as unknown as CopyPlan
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
  const diagram = destinationDiagram(destination)
  if (diagram.regions[destination.region] === undefined) {
    return deny('invalid-destination', `copy destination region '${destination.region}' does not exist`)
  }
  if (destination.kind !== 'proof' && (!Number.isFinite(destination.at.x) || !Number.isFinite(destination.at.y))) {
    return deny('invalid-destination', 'copy destination coordinates must be finite')
  }
  return null
}

/**
 * IDs in an extracted pattern still spell the source IDs because extraction
 * owns a separate namespace. Copy planning makes that namespace genuinely
 * fresh against BOTH live diagrams before handing it to the shared splicer.
 */
function freshlyNamedPattern(extraction: Extraction, source: Diagram, destination: Diagram): DiagramWithBoundary {
  const pattern = extraction.pattern
  const pd = pattern.diagram
  const takenRegions = new Set([...Object.keys(source.regions), ...Object.keys(destination.regions), pd.root])
  const regionMap = new Map<RegionId, RegionId>([[pd.root, pd.root]])
  for (const id of Object.keys(pd.regions).sort()) {
    if (id === pd.root) continue
    const mapped = freshId(takenRegions, `copy_${id}`)
    takenRegions.add(mapped)
    regionMap.set(id, mapped)
  }
  const takenNodes = new Set([...Object.keys(source.nodes), ...Object.keys(destination.nodes)])
  const nodeMap = new Map<NodeId, NodeId>()
  for (const id of Object.keys(pd.nodes).sort()) {
    const mapped = freshId(takenNodes, `copy_${id}`)
    takenNodes.add(mapped)
    nodeMap.set(id, mapped)
  }
  const takenWires = new Set([...Object.keys(source.wires), ...Object.keys(destination.wires)])
  const wireMap = new Map<WireId, WireId>()
  for (const id of Object.keys(pd.wires).sort()) {
    const mapped = freshId(takenWires, `copy_${id}`)
    takenWires.add(mapped)
    wireMap.set(id, mapped)
  }

  const regions: Record<RegionId, Region> = { [pd.root]: { kind: 'sheet' } }
  for (const [id, region] of Object.entries(pd.regions)) {
    if (id === pd.root || region.kind === 'sheet') continue
    const mapped = regionMap.get(id)!
    regions[mapped] = region.kind === 'cut'
      ? { kind: 'cut', parent: regionMap.get(region.parent)! }
      : { kind: 'bubble', parent: regionMap.get(region.parent)!, arity: region.arity }
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, node] of Object.entries(pd.nodes)) {
    const mapped = nodeMap.get(id)!
    switch (node.kind) {
      case 'term': nodes[mapped] = { kind: 'term', region: regionMap.get(node.region)!, term: node.term }; break
      case 'atom': nodes[mapped] = { kind: 'atom', region: regionMap.get(node.region)!, binder: regionMap.get(node.binder)! }; break
      case 'ref': nodes[mapped] = { kind: 'ref', region: regionMap.get(node.region)!, defId: node.defId, arity: node.arity }; break
    }
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(pd.wires)) {
    wires[wireMap.get(id)!] = {
      scope: regionMap.get(wire.scope)!,
      endpoints: wire.endpoints.map((endpoint) => ({ node: nodeMap.get(endpoint.node)!, port: endpoint.port })),
    }
  }
  return mkDiagramWithBoundary(
    mkDiagram({ root: pd.root, regions, nodes, wires }),
    pattern.boundary.map((wire) => wireMap.get(wire)!),
  )
}

function introducedNodes(before: Diagram, after: Diagram): readonly NodeId[] {
  return Object.freeze(Object.keys(after.nodes).filter((id) => before.nodes[id] === undefined).sort())
}

function planStructural(
  kind: StructuralKind,
  source: Diagram,
  selection: SubgraphSelection,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: StructuralKind }>,
): CopyPlan | CopyRefusal {
  const host = destination.kind === 'workspace' ? destination.draft : destination.diagram
  const pattern = freshlyNamedPattern(extraction, source, host)
  try {
    let result: Diagram
    if (destination.kind === 'edit') {
      result = spliceSubgraph(host, destination.region, pattern, extraction.attachments)
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
      result = spliceSubgraph(seeded, destination.region, pattern, loose)
    }
    return finishPlan({
      kind,
      result,
      introduced: introducedNodes(host, result),
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

function frozenAction(steps: readonly ProofStep[]): ProofAction {
  return Object.freeze({
    label: 'Copy selection',
    steps: Object.freeze([...steps]),
    placements: Object.freeze([]),
  })
}

function verifyCandidate(
  before: Diagram,
  intended: Diagram,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
  steps: readonly ProofStep[],
): Candidate | CopyRefusal {
  const action = frozenAction(steps)
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
    if (stateKey(alleged.attachments) !== stateKey(extraction.attachments)) {
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
  compiler.diagram = applyStep(before, step, compiler.destination.ctx, compiler.destination.orientation)
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

function compileNodes(compiler: Compiler): void {
  const pd = compiler.pattern.diagram
  for (const id of Object.keys(pd.nodes).sort()) {
    const node = pd.nodes[id]!
    const region = compiler.regionMap.get(node.region)
    if (region === undefined) throw new Error(`pattern region '${node.region}' was not constructed`)
    let made: { readonly nodes: readonly NodeId[] }
    switch (node.kind) {
      case 'term':
        made = emit(compiler, freePorts(node.term).length === 0
          ? { rule: 'closedTermIntro', region, term: node.term }
          : { rule: 'openTermSpawn', region, term: node.term })
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
    pattern: extraction.pattern,
    destination,
  }
  try {
    compileRegionChildren(compiler, extraction.pattern.diagram.root, destination.region, pairing)
    compileNodes(compiler)
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
      pattern: extraction.pattern,
      destination,
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

/**
 * Exact inverse-fusion normal form: a closed producer feeding a consumer that
 * is exactly that one port. Introducing the fused closed term and fissioning
 * at [] reconstructs both nodes and their bridge without auxiliary residue.
 */
function compileFissionNormalForm(
  before: Diagram,
  extraction: Extraction,
  destination: Extract<CopyDestination, { readonly kind: 'proof' }>,
): ConstructionRecipe | null {
  const pd = extraction.pattern.diagram
  if (childRegions(pd, pd.root).length > 0 || Object.keys(pd.nodes).length !== 2) return null
  for (const [bridgeId, bridge] of Object.entries(pd.wires).sort(([a], [b]) => compareCodeUnits(a, b))) {
    if (extraction.pattern.boundary.includes(bridgeId) || bridge.endpoints.length !== 2 || bridge.scope !== pd.root) continue
    const output = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'output')
    const input = bridge.endpoints.find((endpoint) => endpoint.port.kind === 'freeVar')
    if (output === undefined || input === undefined || output.node === input.node || input.port.kind !== 'freeVar') continue
    const producer = pd.nodes[output.node]
    const consumer = pd.nodes[input.node]
    if (producer?.kind !== 'term' || consumer?.kind !== 'term') continue
    if (freePorts(producer.term).length !== 0) continue
    if (consumer.term.kind !== 'port' || consumer.term.name !== input.port.name) continue

    const compiler: Compiler = {
      diagram: before,
      steps: [],
      regionMap: new Map([[pd.root, destination.region]]),
      nodeMap: new Map(),
      pattern: extraction.pattern,
      destination,
    }
    try {
      const fused = emit(compiler, { rule: 'closedTermIntro', region: destination.region, term: producer.term })
      if (fused.nodes.length !== 1) throw new Error('fission normal form did not introduce exactly one fused node')
      const consumerNode = fused.nodes[0]!
      const split = emit(compiler, { rule: 'fission', node: consumerNode, path: [] })
      if (split.nodes.length !== 1) throw new Error('fission normal form did not create exactly one producer')
      compiler.nodeMap.set(input.node, consumerNode)
      compiler.nodeMap.set(output.node, split.nodes[0]!)
      const attachmentMap = compileWires(compiler, extraction)
      return Object.freeze({
        steps: Object.freeze([...compiler.steps]),
        attachmentMap,
      })
    } catch {
      return null
    }
  }
  return null
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
  const pattern = freshlyNamedPattern(extraction, source, destination.diagram)
  let intended: Diagram
  try {
    intended = spliceSubgraph(destination.diagram, destination.region, pattern, extraction.attachments)
  } catch (error) {
    const classified = classifyStructuralError(error)
    return classified.code === 'invalid-destination' ? classified : deny('invalid-attachment', classified.message)
  }

  const iteration: ProofStep = { rule: 'iteration', sel: selection, target: destination.region }
  const iterated = verifyCandidate(destination.diagram, intended, extraction, destination, [iteration])
  if (!isRefusal(iterated)) {
    return acceptedProofPlan(source, selection, destination, iterated)
  }

  const contextual = compileContextualRelation(destination.diagram, extraction, destination)
  if (contextual !== null && completeAttachmentMap(contextual, extraction)) {
    const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, contextual.steps)
    if (!isRefusal(constructed)) return acceptedProofPlan(source, selection, destination, constructed)
  }

  const fission = compileFissionNormalForm(destination.diagram, extraction, destination)
  if (fission !== null && completeAttachmentMap(fission, extraction)) {
    const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, fission.steps)
    if (!isRefusal(constructed)) return acceptedProofPlan(source, selection, destination, constructed)
  }

  const recipe = compileConstruction(destination.diagram, extraction, destination)
  if (isRefusal(recipe)) return recipe
  if (!completeAttachmentMap(recipe, extraction)) {
    return deny('invalid-attachment', 'ordinary construction did not preserve every crossing attachment identity')
  }
  const constructed = verifyCandidate(destination.diagram, intended, extraction, destination, recipe.steps)
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
  const evidence = (plan as Partial<EvidenceBacked>)[evidenceKey]
  if (evidence === undefined) return deny('invalid-plan', 'copy plan has no revalidation evidence')
  if (stateKey(liveSource) !== evidence.sourceState) {
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
