import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Body, Engine, Leg } from './engine'
import { FRAME_CORNER_W, frameBounds, pkey, portNormal, worldAnchor } from './engine'

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

/** One frame exit per boundary wire, routed by port normal to the nearest edge. */
/** Signed distance to the frame's rounded rectangle (negative inside). */
function frameSdf(px: number, py: number, fb: { minX: number; maxX: number; minY: number; maxY: number }, r: number): number {
  const cx = (fb.minX + fb.maxX) / 2, cy = (fb.minY + fb.maxY) / 2
  const hw = (fb.maxX - fb.minX) / 2 - r, hh = (fb.maxY - fb.minY) / 2 - r
  const qx = Math.abs(px - cx) - hw, qy = Math.abs(py - cy) - hh
  return Math.hypot(Math.max(qx, 0), Math.max(qy, 0)) + Math.min(Math.max(qx, qy), 0) - r
}

export function boundaryExits(e: Engine): BoundaryExit[] {
  const fb = frameBounds(e)
  if (fb === null) return []
  const out: BoundaryExit[] = []
  for (const [wid, bid] of e.boundaryOf) {
    const w0 = e.d.wires[wid]!
    const b = e.bodies.get(bid)!
    const anchorKey = b.kind === 'junction' ? null : pkey(w0.endpoints.find((ep) => ep.node === bid)!.port)
    const p = worldAnchor(b, anchorKey)
    // The exit is where the ray from the frame center through the anchor
    // crosses the ROUNDED frame rectangle — a continuous function of the
    // anchor everywhere, including around corners. (Choosing the nearest
    // edge instead teleports the exit across the frame whenever the anchor
    // crosses a frame diagonal — the reported side-snap.) The rounding is
    // the frame's own drawn corner radius, so exits ride the visible line.
    let dx = p.x - fb.center.x, dy = p.y - fb.center.y
    const dd = Math.hypot(dx, dy)
    if (dd < 1e-9) { dx = 1; dy = 0 } else { dx /= dd; dy /= dd }
    // the SDF grows monotonically along an outward ray from the center, so
    // bisection between the center (inside) and a point past the corner
    // diagonal (outside) converges unconditionally
    let lo = 0, hi = (fb.maxX - fb.minX) * 0.71 + FRAME_CORNER_W
    for (let it = 0; it < 40; it++) {
      const mid = (lo + hi) / 2
      if (frameSdf(fb.center.x + dx * mid, fb.center.y + dy * mid, fb, FRAME_CORNER_W) < 0) lo = mid
      else hi = mid
    }
    const t = (lo + hi) / 2
    const q = { x: fb.center.x + dx * t, y: fb.center.y + dy * t }
    // outward frame normal from the SDF gradient (central differences)
    const h = 1e-3
    const nx = frameSdf(q.x + h, q.y, fb, FRAME_CORNER_W) - frameSdf(q.x - h, q.y, fb, FRAME_CORNER_W)
    const ny = frameSdf(q.x, q.y + h, fb, FRAME_CORNER_W) - frameSdf(q.x, q.y - h, fb, FRAME_CORNER_W)
    const nAng = Math.atan2(ny, nx)
    const ta = b.kind === 'junction' ? Math.atan2(q.y - p.y, q.x - p.x) : portNormal(b, anchorKey, q)
    out.push({ wid, path: hobbyBezier(p, ta, q, nAng + Math.PI), tick: { center: q, angle: nAng + Math.PI / 2 } })
  }
  return out
}

/** Existential stubs: genuine internal singleton wires draw a short loose end
    with an open dot (the ∃ marker), out along the port normal. */
export function existentialStubs(e: Engine): ExStub[] {
  const out: ExStub[] = []
  for (const leg of e.legs) {
    const A: Body = e.bodies.get(leg.from.body)!
    if (!(leg.from.body === leg.to.body && leg.from.key === leg.to.key)) continue
    const p = worldAnchor(A, leg.from.key)
    const n = portNormal(A, leg.from.key, { x: p.x + 1, y: p.y })
    const q = { x: p.x + Math.cos(n) * 10, y: p.y + Math.sin(n) * 10 }
    out.push({ wid: leg.wid, from: p, to: q, dot: q })
  }
  return out
}
