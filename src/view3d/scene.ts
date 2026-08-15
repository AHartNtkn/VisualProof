import type { Diagram, NodeId, WireId } from '../kernel/diagram/diagram'
import { diagramSpec, type Terminal } from './spec'
import { CLEARANCE, UNIT, layoutTree, type TreeLayout } from './layout'
import { steinerNet } from './steiner'
import { clearPoint, routeAll, type Capsule, type EdgeIn, type NetIn } from './route3'
import { add3, cross3, dist3, norm3, scale3, sub3, type Vec3 } from './vec3'

export const RING_SEGMENTS = 32

export type Entity =
  | { kind: 'branch'; key: string; pts: Vec3[] }
  | { kind: 'bead'; key: string; pos: Vec3 }
  | { kind: 'ring'; key: string; node: NodeId; pts: Vec3[] }
  | { kind: 'label'; key: string; node: NodeId; text: string; pos: Vec3 }
  | { kind: 'strand'; key: string; wire: WireId; pts: Vec3[] }
export type Scene3 = { entities: Entity[]; center: Vec3; radius: number }

function ringPolyline(tl: TreeLayout, node: NodeId): Vec3[] {
  const ring = tl.rings.get(node)!
  const anchors = [...ring.anchors.values()]
  if (anchors.length === 0) throw new Error(`scene3: ring ${node} has no anchors`)
  // Reconstruct the rim from center/axis via two rim frame vectors derived
  // from the first anchor (exact: anchors lie on the rim by construction).
  const n1 = norm3(sub3(anchors[0]!, ring.center))
  const n2 = norm3(cross3(ring.axis, n1))
  const pts: Vec3[] = []
  for (let i = 0; i <= RING_SEGMENTS; i++) {
    const a = (2 * Math.PI * i) / RING_SEGMENTS
    pts.push(add3(ring.center, add3(scale3(n1, ring.radius * Math.cos(a)), scale3(n2, ring.radius * Math.sin(a)))))
  }
  return pts
}

export function scene3(d: Diagram): Scene3 {
  const spec = diagramSpec(d)
  const tl = layoutTree(spec)

  const tree: Capsule[] = []
  for (const pr of tl.regions.values()) tree.push({ a: pr.base, b: pr.tip, r: 0 })
  const ringPts = new Map<NodeId, Vec3[]>()
  for (const node of tl.rings.keys()) {
    const pts = ringPolyline(tl, node)
    ringPts.set(node, pts)
    for (let i = 1; i < pts.length; i++) tree.push({ a: pts[i - 1]!, b: pts[i]!, r: 0 })
  }

  const tangentAt = (t: Terminal): Vec3 | null => {
    const ring = tl.rings.get(t.node)
    if (ring === undefined) return null
    return norm3(sub3(tl.anchorOf(t), ring.center))
  }

  const exempt: Vec3[] = []
  const nets: NetIn[] = []
  for (const w of spec.wires) {
    // A wire can have fewer than two NODE endpoints when its remaining ends
    // are boundary entries (kernel two-end floor counts those). It has no
    // in-space curve to draw; its pin/identity node on the line is the
    // visible content. (Boundary-interface rendering is out of this phase's
    // scope — see the plan's closing notes.)
    if (w.terminals.length < 2) continue
    const anchors = w.terminals.map((t) => tl.anchorOf(t))
    anchors.forEach((a) => exempt.push(a))
    if (w.terminals.length === 2) {
      nets.push({ id: w.id, edges: [{ p: anchors[0]!, q: anchors[1]!, tp: tangentAt(w.terminals[0]!), tq: tangentAt(w.terminals[1]!) }] })
      continue
    }
    const net = steinerNet(anchors)
    const junctions = net.junctions.map((j) => clearPoint(j, tree, exempt, CLEARANCE))
    junctions.forEach((j) => exempt.push(j))
    const pos = (i: number): Vec3 => (i < anchors.length ? anchors[i]! : junctions[i - anchors.length]!)
    const edges: EdgeIn[] = net.edges.map(([u, v]) => ({
      p: pos(u), q: pos(v),
      tp: u < anchors.length ? tangentAt(w.terminals[u]!) : null,
      tq: v < anchors.length ? tangentAt(w.terminals[v]!) : null,
    }))
    nets.push({ id: w.id, edges })
  }
  const routed = routeAll(nets, tree, exempt, CLEARANCE)

  const entities: Entity[] = []
  for (const pr of tl.regions.values()) entities.push({ kind: 'branch', key: `b:${pr.region}`, pts: [pr.base, pr.tip] })
  for (const bead of tl.beads) entities.push({ kind: 'bead', key: `d:${bead.region}`, pos: bead.pos })
  for (const [node, pts] of ringPts) entities.push({ kind: 'ring', key: `r:${node}`, node, pts })
  for (const [nid, n] of spec.nodes) {
    if (n.label === null) continue
    const ring = tl.rings.get(nid)!
    const ref = tl.regions.get(n.region)!.ref
    entities.push({ kind: 'label', key: `l:${nid}`, node: nid, text: n.label, pos: add3(ring.center, scale3(ref, ring.radius + 0.4 * UNIT)) })
  }
  for (const [wid, curves] of routed) {
    curves.forEach((pts, i) => entities.push({ kind: 'strand', key: `s:${wid}:${i}`, wire: wid, pts }))
  }

  const rootSphere = tl.spheres.get(spec.root)!
  let radius = 0
  for (const e of entities) {
    const pts = 'pts' in e ? e.pts : [e.pos]
    for (const p of pts) radius = Math.max(radius, dist3(p, rootSphere.center))
  }
  return { entities, center: rootSphere.center, radius: radius + CLEARANCE }
}
