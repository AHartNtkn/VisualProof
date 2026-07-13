import type { Diagram, DiagramNode, Endpoint, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import { freshId } from './freshId'

export type SpliceReservedNamespace = {
  readonly regions?: ReadonlySet<RegionId>
  readonly nodes?: ReadonlySet<string>
  readonly wires?: ReadonlySet<WireId>
}

export type SpliceOptions = {
  readonly binderMap?: ReadonlyMap<RegionId, RegionId>
  readonly reserved?: SpliceReservedNamespace
}

export type MappedSplice = {
  readonly diagram: Diagram
  readonly regionMap: ReadonlyMap<RegionId, RegionId>
  readonly nodeMap: ReadonlyMap<string, string>
  /** Internal wires map to fresh wires; boundary stubs map to their surviving host attachment. */
  readonly wireMap: ReadonlyMap<WireId, WireId>
}

/** Drop the selection's content; touching wires keep only their outside endpoints. */
export function removeSubgraph(d: Diagram, sel: SubgraphSelection): Diagram {
  const c = selectionContents(d, sel)
  const internal = new Set(c.internalWires)
  const regions: Record<RegionId, Region> = {}
  for (const [id, r] of Object.entries(d.regions)) {
    if (!c.allRegions.has(id)) regions[id] = r
  }
  const nodes: Record<string, DiagramNode> = {}
  for (const [id, n] of Object.entries(d.nodes)) {
    if (!c.allNodes.has(id)) nodes[id] = n
  }
  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(d.wires)) {
    if (internal.has(id)) continue
    wires[id] = {
      scope: w.scope,
      endpoints: w.endpoints.filter((ep) => !c.allNodes.has(ep.node)),
    }
  }
  return mkDiagram({ root: d.root, regions, nodes, wires })
}

/**
 * Insert a pattern into a host region. Its ordered boundary incidences are
 * glued to the index-aligned host attachments. When several incidences expose
 * the SAME pattern wire, gluing identifies their host wires: this is the
 * pushout of the two interfaces, not repeated copying of the same endpoints.
 * The quotient keeps the outermost attachment scope and a deterministic
 * survivor id, then copies each boundary stub's endpoints exactly once.
 * Boundary stubs MUST be scoped
 * at the pattern root (the connection seam's quantifier location after the
 * splice IS the attachment wire's scope — a non-root stub scope would assert
 * a location the splice cannot honor; see boundary.ts). Pattern content gets
 * fresh host ids deterministically; the result is re-validated by mkDiagram.
 *
 * With a binder map, mapped stubs are location-transparent layers (not copied
 * as fresh bubbles); their children reparent to the splice region, and atoms
 * bound to them rebind to the host bubbles indicated in the map.
 */
export function spliceSubgraphMapped(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
  options: SpliceOptions = {},
): MappedSplice {
  const binderMap = options.binderMap ?? new Map<RegionId, RegionId>()
  if (host.regions[atRegion] === undefined) {
    throw new DiagramError(`splice region '${atRegion}' does not exist`)
  }
  if (attachments.length !== pattern.boundary.length) {
    throw new DiagramError(`expected ${pattern.boundary.length} attachments, got ${attachments.length}`)
  }
  const pd = pattern.diagram
  const boundarySet = new Set(pattern.boundary)
  for (const b of pattern.boundary) {
    if (pd.wires[b]!.scope !== pd.root) {
      throw new DiagramError(`boundary wire '${b}' is not scoped at the pattern root; not spliceable`)
    }
  }
  for (const a of attachments) {
    const w = host.wires[a]
    if (w === undefined) throw new DiagramError(`attachment wire '${a}' does not exist`)
    if (!isAncestorOrEqual(host, w.scope, atRegion)) {
      throw new DiagramError(`attachment wire '${a}' (scope '${w.scope}') does not enclose splice region '${atRegion}'`)
    }
  }

  // Boundary alias classes induce a quotient on host attachments. Use a tiny
  // union-find over attachment ids: two host wires are identified exactly when
  // two positions exposing the same pattern wire attach to them. Distinct
  // pattern wires may still intentionally attach to one host wire (diagonal
  // instantiation); that does not add another equivalence edge.
  const parent = new Map<WireId, WireId>()
  const find = (w: WireId): WireId => {
    const p = parent.get(w)
    if (p === undefined) { parent.set(w, w); return w }
    if (p === w) return w
    const root = find(p)
    parent.set(w, root)
    return root
  }
  const unite = (a: WireId, b: WireId): void => {
    const ra = find(a), rb = find(b)
    if (ra !== rb) parent.set(rb, ra)
  }
  const firstAttachmentOfStub = new Map<WireId, WireId>()
  pattern.boundary.forEach((stub, i) => {
    const attachment = attachments[i]!
    const first = firstAttachmentOfStub.get(stub)
    if (first === undefined) firstAttachmentOfStub.set(stub, attachment)
    else unite(first, attachment)
  })
  const component = new Map<WireId, WireId[]>()
  for (const attachment of attachments) {
    const root = find(attachment)
    const members = component.get(root)
    if (members === undefined) component.set(root, [attachment])
    else if (!members.includes(attachment)) members.push(attachment)
  }
  const hostImage = new Map<WireId, WireId>()
  for (const members of component.values()) {
    // All attachment scopes enclose atRegion, hence lie on one ancestor chain.
    // Start with first incidence for stable equal-scope tie-breaking and replace
    // it only with a strictly outer scope.
    let survivor = members[0]!
    for (const id of members.slice(1)) {
      const candidate = host.wires[id]!
      const current = host.wires[survivor]!
      if (candidate.scope !== current.scope && isAncestorOrEqual(host, candidate.scope, current.scope)) survivor = id
    }
    for (const id of members) hostImage.set(id, survivor)
  }

  for (const [stub, hb] of binderMap) {
    const ps = pd.regions[stub]
    if (ps === undefined) throw new DiagramError(`binder map stub '${stub}' is not a pattern region`)
    if (ps.kind !== 'bubble') throw new DiagramError(`binder map stub '${stub}' is not a bubble`)
    const target = host.regions[hb]
    if (target === undefined) throw new DiagramError(`binder map target '${hb}' does not exist`)
    if (target.kind !== 'bubble') throw new DiagramError(`binder map target '${hb}' is not a bubble`)
    if (target.arity !== ps.arity) {
      throw new DiagramError(`binder map arity mismatch: stub '${stub}' has arity ${ps.arity}, host bubble '${hb}' has ${target.arity}`)
    }
    if (!isAncestorOrEqual(host, hb, atRegion)) {
      throw new DiagramError(`binder map target '${hb}' does not enclose the splice region '${atRegion}'`)
    }
  }

  // fresh-id maps for pattern regions (except root), nodes, internal wires
  const takenRegions = new Set([...Object.keys(host.regions), ...(options.reserved?.regions ?? [])])
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  // mapped binder stubs are location-transparent layers: their children land
  // at the splice region and atoms bound to them rebind to the host bubble
  for (const stub of binderMap.keys()) regionMap.set(stub, atRegion)
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root || binderMap.has(id)) continue
    const fresh = freshId(takenRegions, id)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
  const takenNodes = new Set([...Object.keys(host.nodes), ...(options.reserved?.nodes ?? [])])
  const nodeMap = new Map<string, string>()
  for (const id of Object.keys(pd.nodes)) {
    const fresh = freshId(takenNodes, id)
    takenNodes.add(fresh)
    nodeMap.set(id, fresh)
  }
  // Mint against the full PRE-QUOTIENT namespace: a wire removed by the
  // pushout must never be resurrected as unrelated copied content.
  const takenWires = new Set([...Object.keys(host.wires), ...(options.reserved?.wires ?? [])])
  const wireMap = new Map<WireId, WireId>()
  pattern.boundary.forEach((stub, index) => {
    wireMap.set(stub, hostImage.get(attachments[index]!) ?? attachments[index]!)
  })
  for (const id of Object.keys(pd.wires)) {
    if (boundarySet.has(id)) continue
    const fresh = freshId(takenWires, id)
    takenWires.add(fresh)
    wireMap.set(id, fresh)
  }

  const regions: Record<RegionId, Region> = { ...host.regions }
  for (const [id, r] of Object.entries(pd.regions)) {
    if (id === pd.root || binderMap.has(id)) continue
    const mapped = regionMap.get(id)!
    if (r.kind === 'sheet') continue // impossible: single sheet is the root
    regions[mapped] = r.kind === 'cut'
      ? { kind: 'cut', parent: regionMap.get(r.parent)! }
      : { kind: 'bubble', parent: regionMap.get(r.parent)!, arity: r.arity }
  }

  // Return-typed switch (no default): a new node kind forces its rebuild here.
  const rebuildNode = (n: DiagramNode): DiagramNode => {
    switch (n.kind) {
      case 'term': return { kind: 'term', region: regionMap.get(n.region)!, term: n.term }
      case 'atom': return { kind: 'atom', region: regionMap.get(n.region)!, binder: binderMap.get(n.binder) ?? regionMap.get(n.binder)! }
      case 'ref': return { kind: 'ref', region: regionMap.get(n.region)!, defId: n.defId, arity: n.arity }
    }
  }
  const nodes: Record<string, DiagramNode> = { ...host.nodes }
  for (const [id, n] of Object.entries(pd.nodes)) {
    nodes[nodeMap.get(id)!] = rebuildNode(n)
  }

  const mapEndpoints = (eps: readonly Endpoint[]): Endpoint[] =>
    eps.map((ep) => ({ node: nodeMap.get(ep.node)!, port: ep.port }))

  const wires: Record<WireId, Wire> = {}
  for (const [id, w] of Object.entries(host.wires)) {
    const image = hostImage.get(id) ?? id
    if (image !== id) continue
    const merged = Object.entries(host.wires)
      .filter(([candidate]) => (hostImage.get(candidate) ?? candidate) === id)
      .flatMap(([, candidate]) => candidate.endpoints)
    wires[id] = merged.length === w.endpoints.length
      ? w
      : { scope: w.scope, endpoints: merged }
  }
  for (const [id, w] of Object.entries(pd.wires)) {
    if (boundarySet.has(id)) continue
    wires[wireMap.get(id)!] = {
      scope: regionMap.get(w.scope)!,
      endpoints: mapEndpoints(w.endpoints),
    }
  }
  const copiedBoundary = new Set<WireId>()
  pattern.boundary.forEach((stubId, i) => {
    if (copiedBoundary.has(stubId)) return
    copiedBoundary.add(stubId)
    const hostWireId = hostImage.get(attachments[i]!) ?? attachments[i]!
    const stub = pd.wires[stubId]!
    const existing = wires[hostWireId]!
    wires[hostWireId] = {
      scope: existing.scope,
      endpoints: [...existing.endpoints, ...mapEndpoints(stub.endpoints)],
    }
  })

  return Object.freeze({
    diagram: mkDiagram({ root: host.root, regions, nodes, wires }),
    regionMap: new Map(regionMap),
    nodeMap: new Map(nodeMap),
    wireMap: new Map(wireMap),
  })
}

/** Ordinary convenience entry: canonical mapped splice without extra reservations. */
export function spliceSubgraph(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
  binderMap: ReadonlyMap<RegionId, RegionId> = new Map(),
): Diagram {
  return spliceSubgraphMapped(host, atRegion, pattern, attachments, { binderMap }).diagram
}
