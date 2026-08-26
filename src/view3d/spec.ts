import type { Diagram, NodeId, Region, RegionId, WireId } from '../kernel/diagram/diagram'
import { portKey } from '../kernel/diagram/diagram'

export type SceneItem = { kind: 'node'; id: NodeId } | { kind: 'branch'; region: RegionId }
export type RegionSpec = { id: RegionId; parent: RegionId | null; items: SceneItem[] }
export type NodeSpec = {
  id: NodeId
  region: RegionId
  kind: 'identity' | 'term' | 'atom' | 'ref'
  label: string | null
  portKeys: string[]
}
export type Terminal = { node: NodeId; portKey: string }
export type WireSpec = { id: WireId; terminals: Terminal[] }
export type DiagramSpec = {
  root: RegionId
  regions: Map<RegionId, RegionSpec>
  nodes: Map<NodeId, NodeSpec>
  wires: WireSpec[]
  escapes: Map<RegionId, number>
}

/** Presentation-topology extraction. Canonical item order: a region's own
    nodes in record order, then its child cuts in record order. */
export function diagramSpec(d: Diagram): DiagramSpec {
  const regions = new Map<RegionId, RegionSpec>()
  for (const [rid, r] of Object.entries(d.regions)) {
    regions.set(rid, { id: rid, parent: r.kind === 'cut' ? r.parent : null, items: [] })
  }
  const nodes = new Map<NodeId, NodeSpec>()
  for (const [nid, n] of Object.entries(d.nodes)) {
    const portKeys =
      n.kind === 'atom' ? ['hd', ...n.sig.args.map((_, i) => `a:${i}`)]
      : n.kind === 'ref' ? n.sig.args.map((_, i) => `a:${i}`)
      : n.kind === 'term' ? ['out', ...Array.from({ length: n.freeArity }, (_, i) => `f:${i}`)]
      : []
    nodes.set(nid, {
      id: nid, region: n.region, kind: n.kind,
      label: n.kind === 'ref' ? n.defId : null, portKeys,
    })
    regions.get(n.region)!.items.push({ kind: 'node', id: nid })
  }
  for (const [rid, r] of Object.entries(d.regions)) {
    if (r.kind === 'cut') regions.get(r.parent)!.items.push({ kind: 'branch', region: rid })
  }

  const wires: WireSpec[] = Object.entries(d.wires).map(([wid, w]) => ({
    id: wid,
    terminals: w.endpoints.map((ep) => ({ node: ep.node, portKey: portKey(ep.port) })),
  }))

  // escapes(r): wires with at least one endpoint inside subtree(r) and one outside.
  const chain = (rid: RegionId): Set<RegionId> => {
    const out = new Set<RegionId>()
    for (let cur: RegionId | null = rid; cur !== null; ) {
      out.add(cur)
      const reg: Region = d.regions[cur]!
      cur = reg.kind === 'cut' ? reg.parent : null
    }
    return out
  }
  const escapes = new Map<RegionId, number>()
  for (const rid of regions.keys()) escapes.set(rid, 0)
  for (const w of wires) {
    const chains = w.terminals.map((t) => chain(nodes.get(t.node)!.region))
    for (const rid of regions.keys()) {
      const inside = chains.filter((c) => c.has(rid)).length
      if (inside > 0 && inside < chains.length) escapes.set(rid, escapes.get(rid)! + 1)
    }
  }
  return { root: d.root, regions, nodes, wires, escapes }
}
