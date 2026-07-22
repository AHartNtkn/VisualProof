import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import { mkDiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Diagram, DiagramNode, NodeId, Region, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { mkDiagram } from '../kernel/diagram/diagram'
import { isAncestorOrEqual } from '../kernel/diagram/regions'
import { spawnBoundRelationNode } from '../kernel/diagram/spawn'
import { extractSubgraph } from '../kernel/diagram/subgraph/extract'
import { freshId, type IdReservation } from '../kernel/diagram/subgraph/freshId'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { spliceSubgraphMapped } from '../kernel/diagram/subgraph/splice'
import type { ComprehensionBinderPair } from '../kernel/rules/comprehension'

export class ComprehensionDependencyError extends Error {
  constructor(message: string) {
    super(message)
    this.name = 'ComprehensionDependencyError'
  }
}

export type ComprehensionDependencyState = {
  readonly pattern: DiagramWithBoundary
  readonly dependencies: readonly ComprehensionBinderPair[]
}

export type AddedComprehensionBoundOccurrence = {
  readonly state: ComprehensionDependencyState
  readonly proxy: RegionId
  readonly node: string
}

export type MergedComprehensionSelection = {
  readonly state: ComprehensionDependencyState
  readonly introduced: readonly NodeId[]
}

function fail(message: string): never {
  throw new ComprehensionDependencyError(message)
}

function frozenPair(proxy: RegionId, target: RegionId): ComprehensionBinderPair {
  return Object.freeze([proxy, target]) as ComprehensionBinderPair
}

function stateOf(
  pattern: DiagramWithBoundary,
  dependencies: readonly ComprehensionBinderPair[],
): ComprehensionDependencyState {
  return Object.freeze({
    pattern,
    dependencies: Object.freeze(dependencies.map(([proxy, target]) => frozenPair(proxy, target))),
  })
}

function instantiationBubble(host: Diagram, instantiationTarget: RegionId): void {
  const target = host.regions[instantiationTarget]
  if (target === undefined) fail(`comprehension instantiation target '${instantiationTarget}' does not exist`)
  if (target.kind !== 'bubble') {
    fail(`comprehension instantiation target '${instantiationTarget}' is not a bubble`)
  }
}

/** Bubble binders properly enclosing the target, in host root-to-target order. */
export function enclosingComprehensionBinders(
  host: Diagram,
  instantiationTarget: RegionId,
): readonly RegionId[] {
  instantiationBubble(host, instantiationTarget)
  const binders: RegionId[] = []
  let current = host.regions[instantiationTarget]!
  while (current.kind !== 'sheet') {
    const parentId = current.parent
    const parent = host.regions[parentId]
    if (parent === undefined) fail(`region '${parentId}' on the instantiation ancestor chain does not exist`)
    if (parent.kind === 'bubble') binders.push(parentId)
    current = parent
  }
  return Object.freeze(binders.reverse())
}

function targetOrder(host: Diagram, instantiationTarget: RegionId): ReadonlyMap<RegionId, number> {
  return new Map(enclosingComprehensionBinders(host, instantiationTarget).map((id, index) => [id, index]))
}

function validateState(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
  requireReferences: boolean,
): void {
  const targetPositions = targetOrder(host, instantiationTarget)
  const diagram = state.pattern.diagram
  const boundary = new Set(state.pattern.boundary)
  const proxies = new Set<RegionId>()
  const hostTargets = new Set<RegionId>()
  let previousTargetPosition = -1
  let container = diagram.root

  for (const [index, [proxyId, targetId]] of state.dependencies.entries()) {
    if (proxies.has(proxyId)) fail(`comprehension dependency has duplicate pattern proxy '${proxyId}'`)
    if (hostTargets.has(targetId)) fail(`comprehension dependency has duplicate host target '${targetId}'`)

    const proxy = diagram.regions[proxyId]
    if (proxy === undefined) fail(`comprehension dependency proxy '${proxyId}' is not a pattern region`)
    if (proxy.kind !== 'bubble') fail(`comprehension dependency proxy '${proxyId}' is not a bubble`)
    const target = host.regions[targetId]
    if (target === undefined) fail(`comprehension dependency host target '${targetId}' does not exist`)
    if (target.kind !== 'bubble') fail(`comprehension dependency host target '${targetId}' is not a bubble`)
    if (proxy.arity !== target.arity) {
      fail(
        `comprehension dependency arity mismatch: proxy '${proxyId}' has ${proxy.arity}, host target '${targetId}' has ${target.arity}`,
      )
    }
    const position = targetPositions.get(targetId)
    if (position === undefined) {
      fail(`comprehension dependency host target '${targetId}' must properly enclose '${instantiationTarget}'`)
    }
    if (position <= previousTargetPosition) {
      fail('comprehension dependencies must follow the host target ancestor chain outermost first')
    }

    const directChildren = Object.entries(diagram.regions).filter(([, region]) =>
      region.kind !== 'sheet' && region.parent === container)
    if (directChildren.length !== 1 || directChildren[0]![0] !== proxyId) {
      const label = index === 0 ? 'root' : `proxy '${container}'`
      fail(`comprehension dependency ${label} must have proxy '${proxyId}' as its only direct child`)
    }
    if (Object.values(diagram.nodes).some((node) => node.region === container)) {
      fail(`comprehension dependency prefix container '${container}' has node content`)
    }
    const nonBoundaryWire = Object.entries(diagram.wires).find(([wireId, wire]) =>
      wire.scope === container && !boundary.has(wireId))
    if (nonBoundaryWire !== undefined) {
      fail(`comprehension dependency prefix container '${container}' scopes non-boundary wire '${nonBoundaryWire[0]}'`)
    }

    proxies.add(proxyId)
    hostTargets.add(targetId)
    previousTargetPosition = position
    container = proxyId
  }

  if (requireReferences) {
    for (const proxy of proxies) {
      const referenced = Object.values(diagram.nodes).some(
        (node) => node.kind === 'atom' && node.binder === proxy,
      )
      if (!referenced) fail(`comprehension dependency proxy '${proxy}' has no bound occurrence`)
    }
  }
}

/** Validate every interaction-layer and kernel-facing dependency invariant. */
export function validateComprehensionDependencies(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
): void {
  validateState(state, host, instantiationTarget, true)
}

export function createComprehensionDependencyState(
  pattern: DiagramWithBoundary,
): ComprehensionDependencyState {
  return stateOf(pattern, [])
}

/** Replace only the formal boundary while preserving the owned diagram identity. */
export function replaceComprehensionDependencyBoundary(
  state: ComprehensionDependencyState,
  boundary: readonly WireId[],
  host: Diagram,
  instantiationTarget: RegionId,
): ComprehensionDependencyState {
  validateState(state, host, instantiationTarget, true)
  const replaced = stateOf(mkDiagramWithBoundary(state.pattern.diagram, boundary), state.dependencies)
  validateState(replaced, host, instantiationTarget, true)
  return replaced
}

function orderedDependencies(
  dependencies: readonly ComprehensionBinderPair[],
  host: Diagram,
  instantiationTarget: RegionId,
): readonly ComprehensionBinderPair[] {
  const positions = targetOrder(host, instantiationTarget)
  return [...dependencies].sort((left, right) => {
    const leftPosition = positions.get(left[1])
    const rightPosition = positions.get(right[1])
    if (leftPosition === undefined) {
      fail(`comprehension dependency host target '${left[1]}' must properly enclose '${instantiationTarget}'`)
    }
    if (rightPosition === undefined) {
      fail(`comprehension dependency host target '${right[1]}' must properly enclose '${instantiationTarget}'`)
    }
    return leftPosition - rightPosition
  })
}

function reparentNode(node: DiagramNode, region: RegionId): DiagramNode {
  switch (node.kind) {
    case 'term': return { kind: 'term', region, term: node.term, freePorts: node.freePorts }
    case 'atom': return { kind: 'atom', region, binder: node.binder }
    case 'ref': return { kind: 'ref', region, defId: node.defId, arity: node.arity }
  }
}

/** Rebuild the dependency prefix and move all root/prefix content into its effective body. */
function repairPrefix(
  pattern: DiagramWithBoundary,
  previousProxies: ReadonlySet<RegionId>,
  dependencies: readonly ComprehensionBinderPair[],
): DiagramWithBoundary {
  const diagram = pattern.diagram
  const body = dependencies.at(-1)?.[0] ?? diagram.root
  const dependencyProxies = new Set(dependencies.map(([proxy]) => proxy))
  const prefixLocations = new Set<RegionId>([diagram.root, ...previousProxies])
  const regions: Record<RegionId, Region> = {}

  for (const [id, region] of Object.entries(diagram.regions)) {
    if (previousProxies.has(id) || dependencyProxies.has(id)) continue
    if (region.kind === 'sheet') {
      regions[id] = region
    } else {
      const parent = prefixLocations.has(region.parent) ? body : region.parent
      regions[id] = region.kind === 'cut'
        ? { kind: 'cut', parent }
        : { kind: 'bubble', parent, arity: region.arity }
    }
  }

  let parent = diagram.root
  for (const [proxy] of dependencies) {
    const region = diagram.regions[proxy]
    if (region === undefined) fail(`comprehension dependency proxy '${proxy}' was removed`)
    if (region.kind !== 'bubble') fail(`comprehension dependency proxy '${proxy}' is not a bubble`)
    regions[proxy] = { kind: 'bubble', parent, arity: region.arity }
    parent = proxy
  }

  const nodes: Record<string, DiagramNode> = {}
  for (const [id, node] of Object.entries(diagram.nodes)) {
    nodes[id] = prefixLocations.has(node.region) ? reparentNode(node, body) : node
  }
  const boundary = new Set(pattern.boundary)
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(diagram.wires)) {
    wires[id] = prefixLocations.has(wire.scope) && !boundary.has(id)
      ? { scope: body, endpoints: wire.endpoints }
      : wire
  }

  return mkDiagramWithBoundary(mkDiagram({ root: diagram.root, regions, nodes, wires }), pattern.boundary)
}

/** Import one accessible host binder, reusing an existing host-target dependency. */
export function importComprehensionDependency(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
  hostTarget: RegionId,
): ComprehensionDependencyState {
  validateState(state, host, instantiationTarget, false)
  const existing = state.dependencies.find(([, target]) => target === hostTarget)
  if (existing !== undefined) return state

  const target = host.regions[hostTarget]
  if (target === undefined || target.kind !== 'bubble') {
    fail(`comprehension dependency host target '${hostTarget}' is not a bubble`)
  }
  if (!targetOrder(host, instantiationTarget).has(hostTarget)) {
    fail(`comprehension dependency host target '${hostTarget}' must properly enclose '${instantiationTarget}'`)
  }

  const diagram = state.pattern.diagram
  const proxy = freshId(new Set(Object.keys(diagram.regions)), 'binder')
  const withProxy = mkDiagramWithBoundary(mkDiagram({
    root: diagram.root,
    regions: {
      ...diagram.regions,
      [proxy]: { kind: 'bubble', parent: diagram.root, arity: target.arity },
    },
    nodes: { ...diagram.nodes },
    wires: { ...diagram.wires },
  }), state.pattern.boundary)
  const dependencies = orderedDependencies(
    [...state.dependencies, frozenPair(proxy, hostTarget)], host, instantiationTarget,
  )
  const previousProxies = new Set([...state.dependencies.map(([id]) => id), proxy])
  const pattern = repairPrefix(withProxy, previousProxies, dependencies)
  const imported = stateOf(pattern, dependencies)
  validateState(imported, host, instantiationTarget, false)
  return imported
}

/**
 * Add an occurrence bound to an imported/reused proxy. Without a selected
 * region, the occurrence lands in the effective body (the innermost proxy,
 * or the pattern root when no dependency exists).
 */
export function addComprehensionBoundOccurrence(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
  hostTarget: RegionId,
  selectedRegion?: RegionId,
  reservation?: IdReservation,
): AddedComprehensionBoundOccurrence {
  const previousBody = state.dependencies.at(-1)?.[0] ?? state.pattern.diagram.root
  const imported = importComprehensionDependency(state, host, instantiationTarget, hostTarget)
  const dependency = imported.dependencies.find(([, target]) => target === hostTarget)!
  const proxy = dependency[0]
  const body = imported.dependencies.at(-1)?.[0] ?? imported.pattern.diagram.root
  const region = selectedRegion === undefined
    || selectedRegion === state.pattern.diagram.root
    || selectedRegion === previousBody
    ? body
    : selectedRegion
  if (imported.pattern.diagram.regions[region] === undefined) {
    fail(`selected comprehension body region '${region}' does not exist`)
  }
  if (!isAncestorOrEqual(imported.pattern.diagram, body, region)) {
    fail(`selected comprehension region '${region}' is not in the effective body '${body}'`)
  }
  const added = spawnBoundRelationNode(imported.pattern.diagram, region, proxy, reservation)
  const pattern = mkDiagramWithBoundary(added.diagram, imported.pattern.boundary)
  const next = stateOf(pattern, imported.dependencies)
  // Imports are valid authoring intermediates before every proxy has acquired
  // an occurrence. Preserve that composability; final validation and
  // materialization require every imported proxy to be referenced.
  validateState(next, host, instantiationTarget, false)
  return Object.freeze({ state: next, proxy, node: added.node })
}

/**
 * Extract an exact selection from the instantiation host and splice it into the
 * dependency body. External binder stubs are merged into canonical proxies;
 * crossing wires become new loose pattern wires, never host attachments.
 */
export function mergeSelectedComprehensionDependencies(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
  source: Diagram,
  selection: SubgraphSelection,
  requestedRegion?: RegionId,
): MergedComprehensionSelection {
  if (source !== host) {
    fail('comprehension selection import requires the instantiation host to be the exact source')
  }
  validateState(state, host, instantiationTarget, true)
  const extraction = extractSubgraph(source, selection)
  if (extraction.binderStubs.length !== extraction.binderAttachments.length) {
    fail('extraction binder stubs and attachments are not index-aligned')
  }

  const previousBody = state.dependencies.at(-1)?.[0] ?? state.pattern.diagram.root
  let imported = state
  for (const hostTarget of extraction.binderAttachments) {
    imported = importComprehensionDependency(imported, host, instantiationTarget, hostTarget)
  }
  const binderMap = new Map<RegionId, RegionId>()
  extraction.binderStubs.forEach((stub, index) => {
    const hostTarget = extraction.binderAttachments[index]!
    const proxy = imported.dependencies.find(([, target]) => target === hostTarget)?.[0]
    if (proxy === undefined) fail(`extraction binder attachment '${hostTarget}' has no imported proxy`)
    binderMap.set(stub, proxy)
  })

  const body = imported.dependencies.at(-1)?.[0] ?? imported.pattern.diagram.root
  const region = requestedRegion === undefined
    || requestedRegion === state.pattern.diagram.root
    || requestedRegion === previousBody
    ? body
    : requestedRegion
  if (imported.pattern.diagram.regions[region] === undefined) {
    fail(`selected comprehension body region '${region}' does not exist`)
  }
  if (!isAncestorOrEqual(imported.pattern.diagram, body, region)) {
    fail(`selected comprehension region '${region}' is not in the effective body '${body}'`)
  }

  const taken = new Set([
    ...Object.keys(source.wires),
    ...Object.keys(imported.pattern.diagram.wires),
    ...Object.keys(extraction.pattern.diagram.wires),
  ])
  const representative = new Map<WireId, WireId>()
  const loose = extraction.pattern.boundary.map((stub, index) => {
    const prior = representative.get(stub)
    if (prior !== undefined) return prior
    const wire = freshId(taken, `copy_boundary_${extraction.attachments[index] ?? index}`)
    taken.add(wire)
    representative.set(stub, wire)
    return wire
  })
  const wires: Record<WireId, Wire> = { ...imported.pattern.diagram.wires }
  for (const wire of loose) wires[wire] = { scope: body, endpoints: [] }
  const seeded = mkDiagram({
    root: imported.pattern.diagram.root,
    regions: { ...imported.pattern.diagram.regions },
    nodes: { ...imported.pattern.diagram.nodes },
    wires,
  })
  const reserved: IdReservation = {
    regions: new Set(Object.keys(source.regions)),
    nodes: new Set(Object.keys(source.nodes)),
    wires: new Set(Object.keys(source.wires)),
  }
  const spliced = spliceSubgraphMapped(
    seeded,
    region,
    extraction.pattern,
    loose,
    { binderMap, reserved },
  )
  const next = stateOf(
    mkDiagramWithBoundary(spliced.diagram, imported.pattern.boundary),
    imported.dependencies,
  )
  validateState(next, host, instantiationTarget, true)
  return Object.freeze({
    state: next,
    introduced: Object.freeze([...spliced.nodeMap.values()].sort()),
  })
}

/** Refuse a direct edit of a proxy while an occurrence still binds to it. */
export function assertComprehensionProxyEditable(
  state: ComprehensionDependencyState,
  proxy: RegionId,
): void {
  if (!state.dependencies.some(([candidate]) => candidate === proxy)) {
    fail(`region '${proxy}' is not a comprehension dependency proxy`)
  }
  if (Object.values(state.pattern.diagram.nodes).some(
    (node) => node.kind === 'atom' && node.binder === proxy,
  )) {
    fail(`comprehension dependency proxy '${proxy}' is still used by a bound occurrence`)
  }
}

/** Derive liveness from edited atoms, prune dead dependencies, and restore the prefix. */
export function reconcileComprehensionDependencies(
  state: ComprehensionDependencyState,
  editedPattern: DiagramWithBoundary,
  host: Diagram,
  instantiationTarget: RegionId,
): ComprehensionDependencyState {
  validateState(state, host, instantiationTarget, true)
  const live = new Set(Object.values(editedPattern.diagram.nodes).flatMap((node) =>
    node.kind === 'atom' ? [node.binder] : []))
  const dependencies = state.dependencies.filter(([proxy]) => live.has(proxy))

  for (const [proxy] of dependencies) {
    const before = state.pattern.diagram.regions[proxy]
    const after = editedPattern.diagram.regions[proxy]
    if (after === undefined) fail(`still-used proxy '${proxy}' was removed`)
    if (
      before?.kind !== 'bubble'
      || after.kind !== 'bubble'
      || before.arity !== after.arity
      || before.parent !== after.parent
    ) {
      fail(`still-used proxy '${proxy}' was mutated`)
    }
  }

  const previousProxies = new Set(state.dependencies.map(([proxy]) => proxy))
  const pattern = repairPrefix(editedPattern, previousProxies, dependencies)
  const reconciled = stateOf(pattern, dependencies)
  validateState(reconciled, host, instantiationTarget, true)
  return reconciled
}

/** Materialize the exact validated kernel binder-pair interface. */
export function materializeComprehensionDependencies(
  state: ComprehensionDependencyState,
  host: Diagram,
  instantiationTarget: RegionId,
): readonly ComprehensionBinderPair[] {
  validateState(state, host, instantiationTarget, true)
  return Object.freeze(state.dependencies.map(([proxy, target]) => frozenPair(proxy, target)))
}
