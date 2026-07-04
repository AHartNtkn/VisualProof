import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, Leg } from './engine'
import { frameBounds, frameSlots, pkey, portNormal, worldAnchor } from './engine'

/**
 * Wire geometry (round-8 lab spec), pure — returns paths, paints nothing.
 * Every line of identity is a Hobby spline (Metafont velocity formula): its
 * endpoint tangents are the port normals at nodes and JUNCTION-computed trunk
 * tangents at branch points, so lines flow tangent-continuously THROUGH a
 * junction. Boundary wires become frame exits; genuine internal singleton
 * wires become existential stubs.
 */

export type WirePath = { from: Vec2; c1: Vec2; c2: Vec2; to: Vec2 }
export type LegGeom = { leg: Leg; pa: Vec2; ta: number; pb: Vec2; tb: number }
export type BoundaryExit = { wid: WireId; path: WirePath; tick: { center: Vec2; angle: number } }
export type ExStub = { wid: WireId; from: Vec2; to: Vec2; dot: Vec2 }

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

/** Hobby's velocity function (Metafont). */
function hobbyRho(theta: number, phi: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  const num = 2 + a * (Math.sin(theta) - b * Math.sin(phi)) * (Math.sin(phi) - b * Math.sin(theta)) * (Math.cos(theta) - Math.cos(phi))
  const den = 1 + (1 - c) * Math.cos(theta) + c * Math.cos(phi)
  return num / den
}

/** Cubic Bézier control points of the Hobby spline from `pa` (tangent `ta`) to
    `pb` (tangent `tb`), tangents being the outward normals at each endpoint. */
export function hobbyBezier(pa: Vec2, ta: number, pb: Vec2, tb: number): WirePath {
  const chord = Math.atan2(pb.y - pa.y, pb.x - pa.x)
  const d = Math.hypot(pb.x - pa.x, pb.y - pa.y)
  const theta = wrap(ta - chord)
  const phi = wrap(chord - (tb + Math.PI))
  const ra = Math.abs(hobbyRho(theta, phi)) * d / 3
  const rb = Math.abs(hobbyRho(phi, theta)) * d / 3
  return {
    from: pa,
    c1: { x: pa.x + Math.cos(ta) * ra, y: pa.y + Math.sin(ta) * ra },
    c2: { x: pb.x + Math.cos(tb) * rb, y: pb.y + Math.sin(tb) * rb },
    to: pb,
  }
}

/** Legs with junction-aware tangents: at a junction the two most-opposite legs
    become one straight trunk (tangents u and u+π), so the line flows through. */
export function computeLegs(e: Engine): LegGeom[] {
  const byJunction = new Map<string, { leg: Leg; at: 'from' | 'to' }[]>()
  for (const leg of e.legs) {
    const fa = e.bodies.get(leg.from.body)!, tb2 = e.bodies.get(leg.to.body)!
    if (fa.kind === 'junction') {
      if (!byJunction.has(fa.id)) byJunction.set(fa.id, [])
      byJunction.get(fa.id)!.push({ leg, at: 'from' })
    }
    if (tb2.kind === 'junction') {
      if (!byJunction.has(tb2.id)) byJunction.set(tb2.id, [])
      byJunction.get(tb2.id)!.push({ leg, at: 'to' })
    }
  }
  const junctionTangent = new Map<string, Map<Leg, number>>()
  for (const [jid, ls] of byJunction) {
    const j = e.bodies.get(jid)!
    const dirs = ls.map(({ leg, at }) => {
      const otherEnd = at === 'from' ? leg.to : leg.from
      const ob = e.bodies.get(otherEnd.body)!
      const q = worldAnchor(ob, otherEnd.key)
      return Math.atan2(q.y - j.pos.y, q.x - j.pos.x)
    })
    // a loose end (degree-1 junction: the ∃ body) has no trunk to pair —
    // its single leg leaves straight toward the port it hangs from
    if (ls.length === 1) {
      junctionTangent.set(jid, new Map([[ls[0]!.leg, dirs[0]!]]))
      continue
    }
    let bi = 0, bj = 1, best = -Infinity
    for (let i = 0; i < dirs.length; i++) for (let k = i + 1; k < dirs.length; k++) {
      const diff = wrap(dirs[i]! - dirs[k]!)
      const score = Math.abs(Math.abs(diff) - Math.PI) * -1 // closest to opposite wins
      if (score > best) { best = score; bi = i; bj = k }
    }
    const u = Math.atan2(
      Math.sin(dirs[bi]!) - Math.sin(dirs[bj]!),
      Math.cos(dirs[bi]!) - Math.cos(dirs[bj]!),
    )
    const m = new Map<Leg, number>()
    ls.forEach(({ leg }, idx) => {
      if (idx === bi) m.set(leg, u)
      else if (idx === bj) m.set(leg, u + Math.PI)
      else m.set(leg, dirs[idx]!)
    })
    junctionTangent.set(jid, m)
  }
  const out: LegGeom[] = []
  for (const leg of e.legs) {
    const A = e.bodies.get(leg.from.body)!, B = e.bodies.get(leg.to.body)!
    if (A === B && leg.from.key === leg.to.key) continue // self-loop -> existential stub
    const pa = worldAnchor(A, leg.from.key), pb = worldAnchor(B, leg.to.key)
    const ta = A.kind === 'junction' ? junctionTangent.get(A.id)!.get(leg)! : portNormal(A, leg.from.key, pb)
    const tb = B.kind === 'junction' ? junctionTangent.get(B.id)!.get(leg)! : portNormal(B, leg.to.key, pa)
    out.push({ leg, pa, ta, pb, tb })
  }
  return out
}

/** Hobby-spline path for every non-boundary, non-stub leg. */
export function legPaths(e: Engine): { wid: WireId; path: WirePath }[] {
  return computeLegs(e).map((g) => ({ wid: g.leg.wid, path: hobbyBezier(g.pa, g.ta, g.pb, g.tb) }))
}

/** One frame exit per boundary wire, terminating at that wire's canonical
    perimeter slot (fixed in boundary order, clockwise from the frame pip). The
    slot placement carries the boundary order, so exits cannot swap as bodies
    move; the exit tangent at the frame is the outward normal at the slot. */
export function boundaryExits(e: Engine): BoundaryExit[] {
  const fb = frameBounds(e)
  if (fb === null) return []
  const slots = frameSlots(fb, e.boundary.length)
  const slotIndex = new Map(e.boundary.map((w, i) => [w, i] as const))
  const out: BoundaryExit[] = []
  for (const [wid, bid] of e.boundaryOf) {
    const w0 = e.d.wires[wid]!
    const b = e.bodies.get(bid)!
    const anchorKey = b.kind === 'junction' ? null : pkey(w0.endpoints.find((ep) => ep.node === bid)!.port)
    const p = worldAnchor(b, anchorKey)
    const slot = slots[slotIndex.get(wid)!]!
    const q = slot.point
    const nAng = slot.normal
    const ta = b.kind === 'junction' ? Math.atan2(q.y - p.y, q.x - p.x) : portNormal(b, anchorKey, q)
    out.push({ wid, path: hobbyBezier(p, ta, q, nAng + Math.PI), tick: { center: q, angle: nAng + Math.PI / 2 } })
  }
  return out
}

/** Existential dots: a dangling wire end is its own body (USER LAW — the
    loose end IS the first-order ∃, homed at the wire's scope). The leg to it
    is drawn by legPaths like any other; here we mark the open dot at the
    degree-1 junction body. */
export function existentialStubs(e: Engine): ExStub[] {
  const degree = new Map<string, number>()
  for (const leg of e.legs) {
    for (const end of [leg.from, leg.to]) {
      const b = e.bodies.get(end.body)!
      if (b.kind === 'junction') degree.set(end.body, (degree.get(end.body) ?? 0) + 1)
    }
  }
  const out: ExStub[] = []
  for (const leg of e.legs) {
    for (const end of [leg.from, leg.to]) {
      const b: Body = e.bodies.get(end.body)!
      if (b.kind === 'junction' && degree.get(end.body) === 1) {
        out.push({ wid: leg.wid, from: b.pos, to: b.pos, dot: b.pos })
      }
    }
  }
  // degree-0 junctions: a bare ∃ (zero-endpoint wire) — the dot IS the wire.
  // The body id is the engine's wire-body convention (`j:<wid>`).
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' && !degree.has(b.id) && b.id.startsWith('j:')) {
      out.push({ wid: b.id.slice(2), from: b.pos, to: b.pos, dot: b.pos })
    }
  }
  return out
}
