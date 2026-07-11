import type { Term } from '../kernel/term/term'
import { freePorts } from '../kernel/term/term'
import type { Diagram, DiagramNode, Endpoint, NodeId, Port, Region, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { mkDiagram, portKey, requiredPorts } from '../kernel/diagram/diagram'
import { deepestCommonAncestor } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { selectionContents } from '../kernel/diagram/subgraph/selection'
import { removeSubgraph } from '../kernel/diagram/subgraph/splice'
import { freshId } from '../kernel/diagram/subgraph/freshId'

/**
 * Construction-mode surgery. These are NOT rules: they build statements
 * before proving starts, and their only obligation is structural validity
 * (every result passes mkDiagram). The session refuses them once a proof is
 * underway.
 */

export function emptyDiagram(): Diagram {
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
}

export function addTermNode(d: Diagram, region: RegionId, term: Term): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: { kind: 'term', region, term } }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  const ports: Port[] = [{ kind: 'output' }, ...freePorts(term).map((name): Port => ({ kind: 'freeVar', name }))]
  for (const port of ports) {
    const w = freshId(takenWires, 'w')
    takenWires.add(w)
    wires[w] = { scope: region, endpoints: [{ node, port }] }
  }
  return { diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }), node }
}

export function addRefNode(d: Diagram, region: RegionId, defId: string, arity: number): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: { kind: 'ref', region, defId, arity } }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (let i = 0; i < arity; i++) {
    const w = freshId(takenWires, 'w')
    takenWires.add(w)
    wires[w] = { scope: region, endpoints: [{ node, port: { kind: 'arg', index: i } }] }
  }
  return { diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }), node }
}

export function addAtomNode(d: Diagram, region: RegionId, binder: RegionId): { diagram: Diagram; node: NodeId } {
  const node = freshId(new Set(Object.keys(d.nodes)), 'n')
  const atom: DiagramNode = { kind: 'atom', region, binder }
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [node]: atom }
  const wires: Record<WireId, Wire> = { ...d.wires }
  const takenWires = new Set(Object.keys(d.wires))
  for (const port of requiredPorts(d, atom)) {
    const wire = freshId(takenWires, 'w')
    takenWires.add(wire)
    wires[wire] = { scope: region, endpoints: [{ node, port }] }
  }
  return {
    node,
    diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }),
  }
}

export type ConstructionHit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

function moveNodeToRegion(node: DiagramNode, region: RegionId): DiagramNode {
  switch (node.kind) {
    case 'term': return { kind: 'term', region, term: node.term }
    case 'atom': return { kind: 'atom', region, binder: node.binder }
    case 'ref': return { kind: 'ref', region, defId: node.defId, arity: node.arity }
  }
}

function subtreeContains(d: Pick<Diagram, 'regions'>, root: RegionId, region: RegionId): boolean {
  let current = region
  for (;;) {
    if (current === root) return true
    const parent = d.regions[current]
    if (parent === undefined || parent.kind === 'sheet') return false
    current = parent.parent
  }
}

function wrap(d: Diagram, sel: SubgraphSelection, make: (parent: RegionId) => Region, base: string): { diagram: Diagram; region: RegionId } {
  selectionContents(d, sel) // validate the complete selection before surgery
  const region = freshId(new Set(Object.keys(d.regions)), base)
  const regions: Record<RegionId, Region> = { ...d.regions, [region]: make(sel.region) }
  const selectedRoots = new Set(sel.regions)
  for (const [id, r] of Object.entries(d.regions)) {
    if (r.kind !== 'sheet' && selectedRoots.has(id)) {
      regions[id] = r.kind === 'cut' ? { kind: 'cut', parent: region } : { kind: 'bubble', parent: region, arity: r.arity }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) nodes[id] = moveNodeToRegion(n, region)
  }
  const selectedWires = new Set(sel.wires)
  const wrappedTree = { regions }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    const enclosed = wire.scope === sel.region && (
      wire.endpoints.length > 0
        ? wire.endpoints.every((endpoint) => subtreeContains(wrappedTree, region, nodes[endpoint.node]!.region))
        : selectedWires.has(id)
    )
    wires[id] = enclosed ? { scope: region, endpoints: wire.endpoints } : wire
  }
  return { diagram: mkDiagram({ root: d.root, regions, nodes, wires }), region }
}

/** Wrap a selection in a SINGLE cut (construction only — proofs use double-cut intro). */
export function addCut(d: Diagram, sel: SubgraphSelection): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'cut', parent }), 'cut')
}

export function addBubble(d: Diagram, sel: SubgraphSelection, arity: number): { diagram: Diagram; region: RegionId } {
  const wrapped = wrap(d, sel, (parent) => ({ kind: 'bubble', parent, arity }), 'bub')
  const directlyWrapped = new Set(sel.nodes)
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, node] of Object.entries(wrapped.diagram.nodes)) {
    nodes[id] = directlyWrapped.has(id) && node.kind === 'atom'
      ? { kind: 'atom', region: wrapped.region, binder: wrapped.region }
      : node
  }
  return {
    region: wrapped.region,
    diagram: mkDiagram({
      root: wrapped.diagram.root,
      regions: { ...wrapped.diagram.regions },
      nodes,
      wires: { ...wrapped.diagram.wires },
    }),
  }
}

/** Identify any number of semantic wires directly. The lexicographically first
    id survives, so the result is independent of selection/gesture order. */
export function joinWires(d: Diagram, wireIds: readonly WireId[]): Diagram {
  if (wireIds.length < 2) throw new Error(`joining needs at least two wires, got ${wireIds.length}`)
  const ids = [...wireIds].sort()
  for (let i = 0; i < ids.length; i++) {
    const id = ids[i]!
    if (i > 0 && id === ids[i - 1]) throw new Error(`wire '${id}' is selected more than once`)
    if (d.wires[id] === undefined) throw new Error(`unknown wire '${id}'`)
  }
  const survivor = ids[0]!
  const scope = ids.slice(1).reduce(
    (current, id) => deepestCommonAncestor(d, current, d.wires[id]!.scope),
    d.wires[survivor]!.scope,
  )
  const endpoints = ids.flatMap((id) => d.wires[id]!.endpoints)
  const merged = new Set(ids)
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (id === survivor) wires[id] = { scope, endpoints }
    else if (!merged.has(id)) wires[id] = wire
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}

/**
 * Identify two individuals: merge the wires holding the two ports into one,
 * scoped at the deepest common scope of the originals (construction-level —
 * the rule-gated counterpart is applyWireJoin).
 */
export function joinPorts(d: Diagram, a: Endpoint, b: Endpoint): Diagram {
  if (a.node === b.node && portKey(a.port) === portKey(b.port)) {
    throw new Error('cannot join a port to the same port')
  }
  const holder = (ep: Endpoint): WireId => {
    // Resolve the port against the node's CURRENT shape first: free-port names
    // are canonical (s0, s1, …) after construction, so an endpoint carrying a
    // pre-construction spelling is invalid input, not a missing wire.
    const node = d.nodes[ep.node]
    if (node === undefined) throw new Error(`no node '${ep.node}' in the diagram`)
    const ports = requiredPorts(d, node)
    if (!ports.some((q) => portKey(q) === portKey(ep.port))) {
      throw new Error(`node '${ep.node}' has no port '${portKey(ep.port)}' (its ports are ${ports.map(portKey).join(', ')}; free-port names are canonical s0, s1, …)`)
    }
    const found = Object.entries(d.wires).find(([, w]) =>
      w.endpoints.some((x) => x.node === ep.node && portKey(x.port) === portKey(ep.port)))
    if (found === undefined) throw new Error(`no wire holds port '${portKey(ep.port)}' of node '${ep.node}'`)
    return found[0]
  }
  const wa = holder(a)
  const wb = holder(b)
  if (wa === wb) return d
  return joinWires(d, [wa, wb])
}

/** Detach one endpoint from a multi-endpoint wire into a fresh singleton wire.
    Both pieces retain the original quantifier scope. */
export function severEndpoint(d: Diagram, wireId: WireId, endpoint: Endpoint): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new Error(`unknown wire '${wireId}'`)
  const index = wire.endpoints.findIndex((candidate) =>
    candidate.node === endpoint.node && portKey(candidate.port) === portKey(endpoint.port))
  if (index < 0) throw new Error(`endpoint is not on wire '${wireId}'`)
  if (wire.endpoints.length < 2) throw new Error('a single loose end cannot be severed further')
  const fresh = freshId(new Set(Object.keys(d.wires)), 'w')
  const detached = wire.endpoints[index]!
  const rest = wire.endpoints.filter((_, candidate) => candidate !== index)
  const wires: Record<WireId, Wire> = {
    ...d.wires,
    [wireId]: { scope: wire.scope, endpoints: rest },
    [fresh]: { scope: wire.scope, endpoints: [detached] },
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes: { ...d.nodes }, wires })
}

/** Remove hits already represented by a selected region subtree. */
export function absorbHits(d: Diagram, hits: readonly ConstructionHit[]): ConstructionHit[] {
  const unique: ConstructionHit[] = []
  for (const hit of hits) {
    if (hit.kind === 'node' && d.nodes[hit.id] === undefined) throw new Error(`unknown node '${hit.id}'`)
    if (hit.kind === 'region') {
      const selected = d.regions[hit.id]
      if (selected === undefined) throw new Error(`unknown region '${hit.id}'`)
      if (selected.kind === 'sheet') throw new Error('the sheet cannot be selected')
    }
    if (hit.kind === 'wire' && d.wires[hit.id] === undefined) throw new Error(`unknown wire '${hit.id}'`)
    if (!unique.some((candidate) => candidate.kind === hit.kind && candidate.id === hit.id)) unique.push(hit)
  }
  const roots = unique.filter((hit): hit is Extract<ConstructionHit, { kind: 'region' }> => hit.kind === 'region').map((hit) => hit.id)
  const strictlyInside = (region: RegionId): boolean => roots.some((root) => root !== region && subtreeContains(d, root, region))
  const insideOrOn = (region: RegionId): boolean => roots.some((root) => subtreeContains(d, root, region))
  return unique.filter((hit) => {
    if (hit.kind === 'region') return !strictlyInside(hit.id)
    if (hit.kind === 'node') return !insideOrOn(d.nodes[hit.id]!.region)
    return !insideOrOn(d.wires[hit.id]!.scope)
  })
}

/** Remove a construction boundary while retaining and promoting its contents. */
export function dissolveRegion(d: Diagram, regionId: RegionId): Diagram {
  const target = d.regions[regionId]
  if (target === undefined) throw new Error(`unknown region '${regionId}'`)
  if (target.kind === 'sheet') throw new Error('the sheet cannot be dissolved')
  const parent = target.parent
  // Atoms are projections of their binder, not independent contents. Once a
  // bubble is dissolved no valid diagram can retain atoms bound by it.
  const dependentAtoms = new Set<NodeId>(Object.entries(d.nodes)
    .filter(([, node]) => node.kind === 'atom' && node.binder === regionId)
    .map(([id]) => id))
  const regions: Record<RegionId, Region> = {}
  for (const [id, region] of Object.entries(d.regions)) {
    if (id === regionId) continue
    regions[id] = region.kind !== 'sheet' && region.parent === regionId
      ? region.kind === 'cut'
        ? { kind: 'cut', parent }
        : { kind: 'bubble', parent, arity: region.arity }
      : region
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, node] of Object.entries(d.nodes)) {
    if (dependentAtoms.has(id)) continue
    nodes[id] = node.region === regionId ? moveNodeToRegion(node, parent) : node
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    const endpoints = wire.endpoints.filter((endpoint) => !dependentAtoms.has(endpoint.node))
    if (wire.endpoints.length > 0 && endpoints.length === 0) continue
    wires[id] = { scope: wire.scope === regionId ? parent : wire.scope, endpoints }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}

/** Endpointful wires whose every endpoint belongs to a deleted node. Existing
    endpointless wires are independent semantic objects and are not orphans. */
export function orphanedWires(d: Diagram, nodeIds: ReadonlySet<NodeId>): WireId[] {
  return Object.entries(d.wires)
    .filter(([, wire]) => wire.endpoints.length > 0 && wire.endpoints.every((endpoint) => nodeIds.has(endpoint.node)))
    .map(([id]) => id)
    .sort()
}

/** Construction deletion over arbitrary anchors. Nodes and selected wires die;
    wires made empty solely by those node deletions die too; selected boundaries
    dissolve deepest-first and promote everything not explicitly deleted. */
export function deleteHits(d: Diagram, hits: readonly ConstructionHit[]): Diagram {
  const normalized = new Map<string, ConstructionHit>()
  for (const hit of hits) {
    if (hit.kind === 'node' && d.nodes[hit.id] === undefined) throw new Error(`unknown node '${hit.id}'`)
    if (hit.kind === 'region') {
      const region = d.regions[hit.id]
      if (region === undefined) throw new Error(`unknown region '${hit.id}'`)
      if (region.kind === 'sheet') throw new Error('the sheet cannot be deleted')
    }
    if (hit.kind === 'wire' && d.wires[hit.id] === undefined) throw new Error(`unknown wire '${hit.id}'`)
    normalized.set(`${hit.kind}:${hit.id}`, hit)
  }
  const selected = [...normalized.values()]
  const deadNodes = new Set(selected.filter((hit): hit is Extract<ConstructionHit, { kind: 'node' }> => hit.kind === 'node').map((hit) => hit.id))
  const deadWires = new Set(selected.filter((hit): hit is Extract<ConstructionHit, { kind: 'wire' }> => hit.kind === 'wire').map((hit) => hit.id))
  for (const id of orphanedWires(d, deadNodes)) deadWires.add(id)

  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, node] of Object.entries(d.nodes)) if (!deadNodes.has(id)) nodes[id] = node
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (deadWires.has(id)) continue
    wires[id] = { scope: wire.scope, endpoints: wire.endpoints.filter((endpoint) => !deadNodes.has(endpoint.node)) }
  }
  let current = mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })

  const depth = (regionId: RegionId): number => {
    let result = 0
    let cursor = regionId
    for (;;) {
      const region = d.regions[cursor]!
      if (region.kind === 'sheet') return result
      result++
      cursor = region.parent
    }
  }
  const boundaries = selected
    .filter((hit): hit is Extract<ConstructionHit, { kind: 'region' }> => hit.kind === 'region')
    .map((hit) => hit.id)
    .sort((a, b) => depth(b) - depth(a) || a.localeCompare(b))
  for (const region of boundaries) current = dissolveRegion(current, region)
  return current
}

/** Move one node between construction regions and maintain the tightest sound
    wire scopes without narrowing a shared wire that remains valid. */
export function reparentNode(d: Diagram, nodeId: NodeId, region: RegionId): Diagram {
  const node = d.nodes[nodeId]
  if (node === undefined) throw new Error(`unknown node '${nodeId}'`)
  if (d.regions[region] === undefined) throw new Error(`unknown region '${region}'`)
  if (node.region === region) return d
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes, [nodeId]: moveNodeToRegion(node, region) }
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (!wire.endpoints.some((endpoint) => endpoint.node === nodeId)) {
      wires[id] = wire
      continue
    }
    if (wire.endpoints.every((endpoint) => endpoint.node === nodeId)) {
      wires[id] = { scope: region, endpoints: wire.endpoints }
      continue
    }
    const endpointRegions = wire.endpoints.map((endpoint) => nodes[endpoint.node]!.region)
    const remainsValid = endpointRegions.every((endpointRegion) => subtreeContains(d, wire.scope, endpointRegion))
    const scope = remainsValid
      ? wire.scope
      : endpointRegions.slice(1).reduce(
        (current, endpointRegion) => deepestCommonAncestor(d, current, endpointRegion),
        endpointRegions[0]!,
      )
    wires[id] = { scope, endpoints: wire.endpoints }
  }
  return mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires })
}

export function deleteSelection(d: Diagram, sel: SubgraphSelection): Diagram {
  return removeSubgraph(d, sel)
}
