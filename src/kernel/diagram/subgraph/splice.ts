import type { Diagram, DiagramNode, Endpoint, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'
import { freshId, type IdReservation } from './freshId'
import { port } from '../../term/term'

export type SpliceOptions = {
  readonly binderMap?: ReadonlyMap<RegionId, RegionId>
  readonly reserved?: IdReservation | undefined
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
 * Boundary stubs are intrinsically scoped at the pattern root by
 * DiagramWithBoundary construction. The assertion below is defensive: the
 * connection seam cannot honor any other scope. Pattern content gets
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
      throw new DiagramError(`invalid DiagramWithBoundary: boundary wire '${b}' is not scoped at the pattern root`)
    }
  }
  for (const a of attachments) {
    const w = host.wires[a]
    if (w === undefined) throw new DiagramError(`attachment wire '${a}' does not exist`)
    if (!isAncestorOrEqual(host, w.scope, atRegion)) {
      throw new DiagramError(`attachment wire '${a}' (scope '${w.scope}') does not enclose splice region '${atRegion}'`)
    }
  }

  // A repeated boundary identity is an equality constraint at the application
  // site, not permission to identify the host wires globally. Keep the first
  // ordered attachment as the copied pattern wire's representative and record
  // every distinct later attachment for one explicit local identity node
  // below. Repeating the same stub/attachment pair adds no new equality.
  const firstAttachmentOfStub = new Map<WireId, WireId>()
  const attachmentsOfStub = new Map<WireId, Set<WireId>>()
  const aliasIncidences: Array<{ representative: WireId; attachment: WireId; position: number }> = []
  pattern.boundary.forEach((stub, i) => {
    const attachment = attachments[i]!
    const first = firstAttachmentOfStub.get(stub)
    if (first === undefined) {
      firstAttachmentOfStub.set(stub, attachment)
      attachmentsOfStub.set(stub, new Set([attachment]))
    } else {
      const seen = attachmentsOfStub.get(stub)!
      if (!seen.has(attachment)) {
        seen.add(attachment)
        aliasIncidences.push({ representative: first, attachment, position: i })
      }
    }
  })

  const binderTargets = new Set<RegionId>()
  for (const [stub, hb] of binderMap) {
    if (binderTargets.has(hb)) {
      throw new DiagramError(`binder map target '${hb}' is used by more than one stub`)
    }
    binderTargets.add(hb)
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
  const takenRegions = new Set(Object.keys(host.regions))
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  // mapped binder stubs are location-transparent layers: their children land
  // at the splice region and atoms bound to them rebind to the host bubble
  for (const stub of binderMap.keys()) regionMap.set(stub, atRegion)
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root || binderMap.has(id)) continue
    const fresh = freshId(takenRegions, id, options.reserved?.regions)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
  const takenNodes = new Set(Object.keys(host.nodes))
  const nodeMap = new Map<string, string>()
  for (const id of Object.keys(pd.nodes)) {
    const fresh = freshId(takenNodes, id, options.reserved?.nodes)
    takenNodes.add(fresh)
    nodeMap.set(id, fresh)
  }
  const aliasNodes = aliasIncidences.map(({ representative, attachment, position }) => {
    const fresh = freshId(takenNodes, `alias_${position}`, options.reserved?.nodes)
    takenNodes.add(fresh)
    return { id: fresh, representative, attachment }
  })
  // Mint against the full PRE-QUOTIENT namespace: a wire removed by the
  // pushout must never be resurrected as unrelated copied content.
  const takenWires = new Set(Object.keys(host.wires))
  const wireMap = new Map<WireId, WireId>()
  pattern.boundary.forEach((stub, index) => {
    if (!wireMap.has(stub)) wireMap.set(stub, attachments[index]!)
  })
  for (const id of Object.keys(pd.wires)) {
    if (boundarySet.has(id)) continue
    const fresh = freshId(takenWires, id, options.reserved?.wires)
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
      case 'term': return { kind: 'term', region: regionMap.get(n.region)!, term: n.term, freePorts: n.freePorts }
      case 'atom': return { kind: 'atom', region: regionMap.get(n.region)!, binder: binderMap.get(n.binder) ?? regionMap.get(n.binder)! }
      case 'ref': return { kind: 'ref', region: regionMap.get(n.region)!, defId: n.defId, arity: n.arity }
    }
  }
  const nodes: Record<string, DiagramNode> = { ...host.nodes }
  for (const [id, n] of Object.entries(pd.nodes)) {
    nodes[nodeMap.get(id)!] = rebuildNode(n)
  }
  for (const alias of aliasNodes) {
    nodes[alias.id] = { kind: 'term', region: atRegion, term: port('s0'), freePorts: ['s0'] }
  }

  const mapEndpoints = (eps: readonly Endpoint[]): Endpoint[] =>
    eps.map((ep) => ({ node: nodeMap.get(ep.node)!, port: ep.port }))

  const wires: Record<WireId, Wire> = { ...host.wires }
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
    const hostWireId = attachments[i]!
    const stub = pd.wires[stubId]!
    const existing = wires[hostWireId]!
    wires[hostWireId] = {
      scope: existing.scope,
      endpoints: [...existing.endpoints, ...mapEndpoints(stub.endpoints)],
    }
  })
  for (const alias of aliasNodes) {
    const representative = wires[alias.representative]!
    const attachment = wires[alias.attachment]!
    if (alias.representative === alias.attachment) {
      wires[alias.representative] = {
        scope: representative.scope,
        endpoints: [
          ...representative.endpoints,
          { node: alias.id, port: { kind: 'output' } },
          { node: alias.id, port: { kind: 'freeVar', name: 's0' } },
        ],
      }
    } else {
      wires[alias.representative] = {
        scope: representative.scope,
        endpoints: [...representative.endpoints, { node: alias.id, port: { kind: 'output' } }],
      }
      wires[alias.attachment] = {
        scope: attachment.scope,
        endpoints: [...attachment.endpoints, { node: alias.id, port: { kind: 'freeVar', name: 's0' } }],
      }
    }
  }

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
