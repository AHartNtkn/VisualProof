import type { Diagram, NodeId, WireId } from '../kernel/diagram/diagram'
import { diagramSpec } from './spec'
import { CLEARANCE, UNIT, layoutTree, type TreeLayout } from './layout'
import { steinerNet } from './steiner'
import { routeAll, type Capsule, type NetIn } from './route3'
import { add3, anyPerp, cross3, dist3, dot3, len3, norm3, scale3, sub3, v3, type Vec3 } from './vec3'

export const RING_SEGMENTS = 32

export type Entity =
  | { kind: 'branch'; key: string; pts: Vec3[] }
  | { kind: 'bead'; key: string; pos: Vec3 }
  /** An identity node's marker on its line (USER law 2026-08-15: identity
      nodes draw small pips over the branches). `ownerWire`: the first wire
      bound there — the 2D bodyStroke hue rule. */
  | { kind: 'pip'; key: string; node: NodeId; ownerWire: WireId | null; pos: Vec3 }
  /** `headWire`: the wire bound to an atom's head port — the ring strokes in
      that wire's order hue, matching the 2D painter. Null for refs. */
  | { kind: 'ring'; key: string; node: NodeId; headWire: WireId | null; pts: Vec3[] }
  | { kind: 'label'; key: string; node: NodeId; text: string; pos: Vec3 }
  | { kind: 'strand'; key: string; wire: WireId; pts: Vec3[] }
export type Scene3 = { entities: Entity[]; center: Vec3; radius: number }

function ringPolyline(tl: TreeLayout, node: NodeId): Vec3[] {
  const ring = tl.rings.get(node)!
  const anchors = [...ring.anchors.values()]
  // Reconstruct the rim from center/axis via two rim frame vectors. A ring
  // with anchors derives its frame from the first anchor (exact: anchors lie
  // on the rim by construction); a 0-ary node has no anchors, so the frame
  // falls back to an arbitrary perpendicular of the branch axis.
  const n1 = anchors.length === 0 ? anyPerp(ring.axis) : norm3(sub3(anchors[0]!, ring.center))
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
  for (const pr of tl.regions.values()) tree.push({ a: pr.base, b: pr.tip, r: 0, g: `reg:${pr.region}` })
  const ringPts = new Map<NodeId, Vec3[]>()
  for (const [node, ring] of tl.rings) {
    const pts = ringPolyline(tl, node)
    ringPts.set(node, pts)
    for (let i = 1; i < pts.length; i++) tree.push({ a: pts[i - 1]!, b: pts[i]!, r: 0, g: `ring:${node}` })
    // The disc INTERIOR is solid to wires (USER 2026-08-15: wires connect
    // only to ring exteriors, never thread through them). A disc has no
    // capsule form, so cover it with diameter spokes spaced closely enough
    // at the rim (≤ δ apart) that no δ-cleared curve fits between them.
    const n1 = anyPerp(ring.axis)
    const n2 = norm3(cross3(ring.axis, n1))
    const spokes = Math.max(2, Math.ceil((Math.PI * ring.radius) / CLEARANCE))
    for (let s = 0; s < spokes; s++) {
      const a = (Math.PI * s) / spokes
      const dir = add3(scale3(n1, Math.cos(a)), scale3(n2, Math.sin(a)))
      tree.push({
        a: add3(ring.center, scale3(dir, ring.radius)),
        b: add3(ring.center, scale3(dir, -ring.radius)),
        r: 0,
        g: `ring:${node}`,
      })
    }
  }

  const nets: NetIn[] = []
  for (const w of spec.wires) {
    // A wire can have fewer than two NODE endpoints when its remaining ends
    // are boundary entries (kernel two-end floor counts those). It has no
    // in-space curve to draw; its pin/identity node on the line is the
    // visible content. (Boundary-interface rendering is out of this phase's
    // scope — see the plan's closing notes.)
    if (w.terminals.length < 2) continue
    const anchors = w.terminals.map((t) => tl.anchorOf(t))
    // Departure normal per terminal. Ring anchors leave along the OUTWARD
    // radial (USER law 2026-08-15: the branch-facing side of an application
    // circle is its interior — wires connect only from outside). Identity
    // anchors leave perpendicular to their line, toward the wire's other
    // content when that direction exists; a same-line wire falls back to
    // the region's reference normal, shared by both ends so its arch bows
    // to one side (USER law: a wire is never parallel-and-overlapping with
    // a branch).
    const departure = (t: number): Vec3 => {
      const term = w.terminals[t]!
      const ring = tl.rings.get(term.node)
      if (ring !== undefined) return norm3(sub3(anchors[t]!, ring.center))
      const pr = tl.regions.get(spec.nodes.get(term.node)!.region)!
      let cen = v3(0, 0, 0)
      let n = 0
      for (let o = 0; o < anchors.length; o++) {
        if (o === t) continue
        cen = add3(cen, anchors[o]!)
        n++
      }
      const raw = sub3(scale3(cen, 1 / n), anchors[t]!)
      const perp = sub3(raw, scale3(pr.dir, dot3(raw, pr.dir)))
      return len3(perp) > 1e-9 ? norm3(perp) : pr.ref
    }
    const tangents = w.terminals.map((_, t) => departure(t))
    let junctions: Vec3[] = []
    let edges: (readonly [number, number])[] = [[0, 1]]
    if (w.terminals.length > 2) {
      const net = steinerNet(anchors)
      junctions = [...net.junctions]
      edges = net.edges.map(([u, vv]) => [u, vv] as const)
    }
    // USER law (2026-08-15): a terminal always connects at the END of a
    // branch, from the exterior. EVERY terminal hangs off a standoff
    // junction two clearances out along its departure normal, joined by a
    // short straight leaf — the visible connection at a rim or line is
    // always an outward stub, and the routed web only ever meets the
    // stub's outer end.
    for (let t = 0; t < anchors.length; t++) {
      const jv = anchors.length + junctions.length
      junctions.push(add3(anchors[t]!, scale3(departure(t), 2 * CLEARANCE)))
      edges = edges.map(([u, vv]) => [u === t ? jv : u, vv === t ? jv : vv] as const)
      edges.push([t, jv] as const)
    }
    nets.push({ id: w.id, anchors, tangents, junctions, edges })
  }
  const routed = routeAll(nets, tree, CLEARANCE)

  const entities: Entity[] = []
  for (const pr of tl.regions.values()) entities.push({ kind: 'branch', key: `b:${pr.region}`, pts: [pr.base, pr.tip] })
  for (const bead of tl.beads) entities.push({ kind: 'bead', key: `d:${bead.region}`, pos: bead.pos })
  const ownerWireOf = new Map<NodeId, WireId>()
  for (const w of spec.wires) {
    for (const t of w.terminals) {
      if (spec.nodes.get(t.node)!.kind === 'identity' && !ownerWireOf.has(t.node)) ownerWireOf.set(t.node, w.id)
    }
  }
  for (const [nid, pos] of tl.identityAnchor) {
    entities.push({ kind: 'pip', key: `p:${nid}`, node: nid, ownerWire: ownerWireOf.get(nid) ?? null, pos })
  }
  const headWireOf = new Map<NodeId, WireId>()
  for (const w of spec.wires) {
    for (const t of w.terminals) if (t.portKey === 'hd') headWireOf.set(t.node, w.id)
  }
  for (const [node, pts] of ringPts) {
    entities.push({ kind: 'ring', key: `r:${node}`, node, headWire: headWireOf.get(node) ?? null, pts })
  }
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
