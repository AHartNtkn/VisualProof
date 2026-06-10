import type { Diagram, DiagramNode, Endpoint, Region, RegionId, Wire, WireId } from '../diagram'
import { DiagramError, mkDiagram } from '../diagram'
import { isAncestorOrEqual } from '../regions'
import type { DiagramWithBoundary } from '../boundary'
import type { SubgraphSelection } from './selection'
import { selectionContents } from './selection'

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

function freshId(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate)) return candidate
  }
}

/**
 * Insert a pattern into a host region, merging each boundary stub's endpoints
 * into the index-aligned host attachment wire. Boundary stubs MUST be scoped
 * at the pattern root (the connection seam's quantifier location after the
 * splice IS the attachment wire's scope — a non-root stub scope would assert
 * a location the splice cannot honor; see boundary.ts). Pattern content gets
 * fresh host ids deterministically; the result is re-validated by mkDiagram.
 */
export function spliceSubgraph(
  host: Diagram,
  atRegion: RegionId,
  pattern: DiagramWithBoundary,
  attachments: readonly WireId[],
): Diagram {
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

  // fresh-id maps for pattern regions (except root), nodes, internal wires
  const takenRegions = new Set(Object.keys(host.regions))
  const regionMap = new Map<RegionId, RegionId>([[pd.root, atRegion]])
  for (const id of Object.keys(pd.regions)) {
    if (id === pd.root) continue
    const fresh = freshId(takenRegions, id)
    takenRegions.add(fresh)
    regionMap.set(id, fresh)
  }
  const takenNodes = new Set(Object.keys(host.nodes))
  const nodeMap = new Map<string, string>()
  for (const id of Object.keys(pd.nodes)) {
    const fresh = freshId(takenNodes, id)
    takenNodes.add(fresh)
    nodeMap.set(id, fresh)
  }
  const takenWires = new Set(Object.keys(host.wires))
  const wireMap = new Map<WireId, WireId>()
  for (const id of Object.keys(pd.wires)) {
    if (boundarySet.has(id)) continue
    const fresh = freshId(takenWires, id)
    takenWires.add(fresh)
    wireMap.set(id, fresh)
  }

  const regions: Record<RegionId, Region> = { ...host.regions }
  for (const [id, r] of Object.entries(pd.regions)) {
    if (id === pd.root) continue
    const mapped = regionMap.get(id)!
    if (r.kind === 'sheet') continue // impossible: single sheet is the root
    regions[mapped] = r.kind === 'cut'
      ? { kind: 'cut', parent: regionMap.get(r.parent)! }
      : { kind: 'bubble', parent: regionMap.get(r.parent)!, arity: r.arity }
  }

  const nodes: Record<string, DiagramNode> = { ...host.nodes }
  for (const [id, n] of Object.entries(pd.nodes)) {
    const mapped = nodeMap.get(id)!
    nodes[mapped] = n.kind === 'term'
      ? { kind: 'term', region: regionMap.get(n.region)!, term: n.term }
      : { kind: 'atom', region: regionMap.get(n.region)!, binder: regionMap.get(n.binder)! }
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
  pattern.boundary.forEach((stubId, i) => {
    const hostWireId = attachments[i]!
    const stub = pd.wires[stubId]!
    const existing = wires[hostWireId]!
    wires[hostWireId] = {
      scope: existing.scope,
      endpoints: [...existing.endpoints, ...mapEndpoints(stub.endpoints)],
    }
  })

  return mkDiagram({ root: host.root, regions, nodes, wires })
}
