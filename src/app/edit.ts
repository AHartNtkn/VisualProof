import type { Diagram, DiagramNode, Endpoint, NodeId, Region, RegionId, Wire, WireId } from '../kernel/diagram/diagram'
import { mkDiagram, portKey, requiredPorts } from '../kernel/diagram/diagram'
import type { Sig } from '../kernel/diagram/sig'
import { sigEquals, sigKey } from '../kernel/diagram/sig'
import { derivedScope, isAncestorOrEqual, wireVisibleAt } from '../kernel/diagram/regions'
import type { SubgraphSelection } from '../kernel/diagram/subgraph/selection'
import { selectionContents } from '../kernel/diagram/subgraph/selection'
import { removeSubgraph } from '../kernel/diagram/subgraph/splice'
import { freshId } from '../kernel/diagram/subgraph/freshId'
import type { PartsInProgress } from '../kernel/rules/wire-ends'
import { completeWireEnds, endpointDca } from '../kernel/rules/wire-ends'

/**
 * Construction-mode surgery. These are NOT rules: they build statements
 * before proving starts, and their only obligation is structural validity
 * (every result passes mkDiagram). The session refuses them once a proof is
 * underway.
 */

export function emptyDiagram(): Diagram {
  return mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
}

export type ConstructionHit =
  | { readonly kind: 'node'; readonly id: NodeId }
  | { readonly kind: 'region'; readonly id: RegionId }
  | { readonly kind: 'wire'; readonly id: WireId }

function moveNodeToRegion(node: DiagramNode, region: RegionId): DiagramNode {
  switch (node.kind) {
    case 'term': return { kind: 'term', region, term: node.term, freeArity: node.freeArity }
    case 'atom': return { kind: 'atom', region, sig: node.sig }
    case 'ref': return { kind: 'ref', region, defId: node.defId, sig: node.sig }
    case 'identity': return { kind: 'identity', region, sig: node.sig, arity: node.arity }
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
      regions[id] = { kind: 'cut', parent: region }
    }
  }
  const selectedNodes = new Set(sel.nodes)
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  for (const [id, n] of Object.entries(d.nodes)) {
    if (selectedNodes.has(id)) nodes[id] = moveNodeToRegion(n, region)
  }
  // Wires are untouched: a wire whose every incidence moves inside follows
  // its nodes into the new region, and one with an incidence left outside
  // keeps its quantifier there — both are what the derived scope computes.
  return { diagram: mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } }), region }
}

/** Wrap a selection in a SINGLE cut (construction only — proofs use double-cut intro). */
export function addCut(d: Diagram, sel: SubgraphSelection): { diagram: Diagram; region: RegionId } {
  return wrap(d, sel, (parent) => ({ kind: 'cut', parent }), 'cut')
}

/**
 * Introduce a fresh wire of sort `sig` at `region`, drawn as the bare
 * two-pin segment that holds its quantifier there. At a relation sig this IS
 * the second-order existential variable (the old "bubble"), and atoms attach
 * their head to it; at IOTA it is a bare individual wire. A bare segment is
 * a vacuous existential, deletable by vacuity — the construction-level
 * counterpart of vacuity insertion.
 */
export function addRelationWire(d: Diagram, region: RegionId, sig: Sig): { diagram: Diagram; wire: WireId } {
  if (d.regions[region] === undefined) throw new Error(`unknown region '${region}'`)
  const wire = freshId(new Set(Object.keys(d.wires)), 'w')
  const nodes: Record<NodeId, DiagramNode> = { ...d.nodes }
  const taken = new Set(Object.keys(nodes))
  const endpoints: Endpoint[] = []
  for (let end = 0; end < 2; end++) {
    const pin = freshId(taken, 'pin')
    taken.add(pin)
    nodes[pin] = { kind: 'identity', region, sig, arity: 1 }
    endpoints.push({ node: pin, port: { kind: 'identity', index: 0 } })
  }
  const wires: Record<WireId, Wire> = { ...d.wires, [wire]: { sig, endpoints } }
  return { diagram: mkDiagram({ root: d.root, regions: { ...d.regions }, nodes, wires }), wire }
}

/**
 * Construction-level identity placement over any number of wires: two or
 * more equates them, one pins a wire at `region`, none places a typed point.
 * Unlike Rule 4 this is available at either polarity because edit mode
 * authors a statement rather than deriving one. `sig` is inferred from the
 * wires when there are any, and must be given for a bare point.
 */
export function addIdentity(
  diagram: Diagram,
  region: RegionId,
  wires: readonly WireId[],
  sig?: Sig,
): Diagram {
  if (diagram.regions[region] === undefined) throw new Error(`unknown region '${region}'`)
  if (new Set(wires).size !== wires.length) {
    throw new Error('identity construction requires distinct wires')
  }
  const selected = wires.map((wireId) => {
    const wire = diagram.wires[wireId]
    if (wire === undefined) throw new Error(`unknown wire '${wireId}'`)
    return [wireId, wire] as const
  })
  const nodeSig = sig ?? selected[0]?.[1].sig
  if (nodeSig === undefined) {
    throw new Error('identity construction over no wires needs an explicit signature')
  }
  for (const [wireId, wire] of selected) {
    if (!sigEquals(wire.sig, nodeSig)) {
      throw new Error(
        `identity construction wires must have the same signature; `
        + `the identity has '${sigKey(nodeSig)}' but '${wireId}' has '${sigKey(wire.sig)}'`,
      )
    }
    if (!wireVisibleAt(diagram, wireId, region)) {
      throw new Error(
        `identity construction wire '${wireId}' scoped at `
        + `'${derivedScope(diagram, wireId)}' is not visible at '${region}'`,
      )
    }
  }

  const node = freshId(new Set(Object.keys(diagram.nodes)), 'identity')
  const nodes: Record<NodeId, DiagramNode> = {
    ...diagram.nodes,
    [node]: { kind: 'identity', region, sig: nodeSig, arity: wires.length },
  }
  const rebuiltWires: Record<WireId, Wire> = { ...diagram.wires }
  wires.forEach((wireId, index) => {
    const wire = rebuiltWires[wireId]!
    rebuiltWires[wireId] = {
      sig: wire.sig,
      endpoints: [...wire.endpoints, { node, port: { kind: 'identity', index } }],
    }
  })
  return mkDiagram({
    root: diagram.root,
    regions: { ...diagram.regions },
    nodes,
    wires: rebuiltWires,
  })
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
  const sig = d.wires[survivor]!.sig
  for (const id of ids.slice(1)) {
    const candidate = d.wires[id]!.sig
    if (!sigEquals(sig, candidate)) {
      throw new Error(
        `joining wires requires the same signature; '${survivor}' has '${sigKey(sig)}' `
        + `but '${id}' has '${sigKey(candidate)}'`,
      )
    }
  }
  // The merged incidences carry the merged quantifier: their deepest common
  // ancestor is the deepest common ancestor of the old derived scopes, pins
  // included — they are endpoints and merge along with the rest.
  const endpoints = ids.flatMap((id) => d.wires[id]!.endpoints)
  const merged = new Set(ids)
  const wires: Record<WireId, Wire> = {}
  for (const [id, wire] of Object.entries(d.wires)) {
    if (id === survivor) wires[id] = { sig: d.wires[survivor]!.sig, endpoints }
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
    const ports = requiredPorts(node)
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

/** Detach one endpoint from a wire into a fresh wire of its own. Both pieces
    keep the original quantifier scope, held by pins where the remaining
    incidences no longer reach it. */
export function severEndpoint(d: Diagram, wireId: WireId, endpoint: Endpoint): Diagram {
  const wire = d.wires[wireId]
  if (wire === undefined) throw new Error(`unknown wire '${wireId}'`)
  const index = wire.endpoints.findIndex((candidate) =>
    candidate.node === endpoint.node && portKey(candidate.port) === portKey(endpoint.port))
  if (index < 0) throw new Error(`endpoint is not on wire '${wireId}'`)
  const scope = derivedScope(d, wireId)
  const fresh = freshId(new Set(Object.keys(d.wires)), 'w')
  const detached = wire.endpoints[index]!
  const rest = wire.endpoints.filter((_, candidate) => candidate !== index)
  const parts: PartsInProgress = {
    regions: { ...d.regions },
    nodes: { ...d.nodes },
    wires: {
      ...d.wires,
      [wireId]: { sig: wire.sig, endpoints: rest },
      [fresh]: { sig: wire.sig, endpoints: [detached] },
    },
  }
  completeWireEnds(parts, wireId, scope, 'severing')
  completeWireEnds(parts, fresh, scope, 'severing')
  return mkDiagram({ root: d.root, ...parts })
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
    return !insideOrOn(derivedScope(d, hit.id))
  })
}

/** Remove a construction boundary while retaining and promoting its contents. */
export function dissolveRegion(d: Diagram, regionId: RegionId): Diagram {
  const target = d.regions[regionId]
  if (target === undefined) throw new Error(`unknown region '${regionId}'`)
  if (target.kind === 'sheet') throw new Error('the sheet cannot be dissolved')
  const parent = target.parent
  const regions: Record<RegionId, Region> = {}
  for (const [id, region] of Object.entries(d.regions)) {
    if (id === regionId) continue
    regions[id] = region.kind !== 'sheet' && region.parent === regionId
      ? { kind: 'cut', parent }
      : region
  }
  const nodes: Record<NodeId, DiagramNode> = {}
  for (const [id, node] of Object.entries(d.nodes)) {
    nodes[id] = node.region === regionId ? moveNodeToRegion(node, parent) : node
  }
  // Wires are untouched: a quantifier living in the dissolving boundary rides
  // its nodes up to the parent, which is where the derived scope now lands.
  return mkDiagram({ root: d.root, regions, nodes, wires: { ...d.wires } })
}

/** Wires whose every endpoint belongs to a deleted node: nothing of them
    survives the deletion, so they die with their ends. */
export function orphanedWires(d: Diagram, nodeIds: ReadonlySet<NodeId>): WireId[] {
  return Object.entries(d.wires)
    .filter(([, wire]) => wire.endpoints.every((endpoint) => nodeIds.has(endpoint.node)))
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
    wires[id] = { sig: wire.sig, endpoints: wire.endpoints.filter((endpoint) => !deadNodes.has(endpoint.node)) }
  }
  // A surviving wire that loses ends keeps the quantifier it had: pins at the
  // old derived scope replace the lost incidences, down to the two-end floor.
  const parts: PartsInProgress = { regions: { ...d.regions }, nodes, wires }
  for (const [id, wire] of Object.entries(d.wires)) {
    if (deadWires.has(id)) continue
    if (!wire.endpoints.some((endpoint) => deadNodes.has(endpoint.node))) continue
    completeWireEnds(parts, id, derivedScope(d, id), 'deletion')
  }
  let current = mkDiagram({ root: d.root, ...parts })

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
  const parts: PartsInProgress = {
    regions: { ...d.regions },
    nodes: { ...d.nodes, [nodeId]: moveNodeToRegion(node, region) },
    wires: { ...d.wires },
  }
  for (const [id, wire] of Object.entries(d.wires)) {
    if (!wire.endpoints.some((endpoint) => endpoint.node === nodeId)) continue
    const before = derivedScope(d, id)
    const after = endpointDca(parts, wire.endpoints)
    // A move that narrows a wire still sound where it was keeps it there,
    // held by a pin; a move that carries an end out of the old scope takes
    // the quantifier with it, which is the derived scope of the new ends.
    if (after !== null && after !== before && isAncestorOrEqual(d, before, after)) {
      completeWireEnds(parts, id, before, 'reparenting')
    }
  }
  return mkDiagram({ root: d.root, ...parts })
}

export function deleteSelection(d: Diagram, sel: SubgraphSelection): Diagram {
  return removeSubgraph(d, sel)
}
