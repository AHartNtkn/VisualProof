import type { WireId } from '../kernel/diagram/diagram'
import type { Vec2 } from './vec'
import type { Engine, Leg } from './engine'
import { frameBounds, frameSlots, worldBindAnchor } from './engine'

/**
 * Wire geometry over the PLAN-21 chains, pure — returns paths, paints
 * nothing. Every chain segment is emitted as a Hobby spline whose endpoint
 * tangents come from the chain itself: port normals at bind terminals,
 * Catmull-style through-directions at interior points — so the drawn line is
 * the relaxed physical wire, smoothed. Boundary wires end in frame exits
 * (their final segment is emitted by boundaryExits with the slot tick);
 * homed ∃ ends and bare wires become existential dots.
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
    `pb` (tangent `tb`), tangents being the outward directions at each end. */
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

/** Per-chain outward tangents for the edge (v -> n): port normal at binds,
    Catmull through-direction at degree-2 interior points, and at junctions
    the round-8 TRIBUTARY rule — the two most-opposite branches flow through
    as one stream along a RELAXED axis (phi, low-passed orientation tensor:
    inertia prevents the pairing flips that made junctions jump), side
    branches merge tangent to it with a weight that vanishes exactly where
    the side choice would flip. Tangents are clamped inside the Hobby
    no-loop bound against the chord. */
const wrapAxis = (x: number): number => Math.atan2(Math.sin(2 * x), Math.cos(2 * x)) / 2

function junctionPhi(ch: NonNullable<ReturnType<Engine['chains']['get']>>, v: number): number {
  if (ch.phis === undefined) ch.phis = new Map()
  let c2 = 0, s2 = 0
  for (const n of ch.adj[v]!) {
    const a = Math.atan2(ch.pts[n]!.y - ch.pts[v]!.y, ch.pts[n]!.x - ch.pts[v]!.x)
    c2 += Math.cos(2 * a)
    s2 += Math.sin(2 * a)
  }
  const anis = Math.hypot(c2, s2) / ch.adj[v]!.length
  const prev = ch.phis.get(v)
  if (prev === undefined) {
    const phi0 = anis < 1e-9 ? 0 : Math.atan2(s2, c2) / 2
    ch.phis.set(v, phi0)
    return phi0
  }
  if (anis < 1e-9) return prev
  const target = Math.atan2(s2, c2) / 2
  const next = wrapAxis(prev + wrapAxis(target - prev) * Math.min(1, anis) * 0.2)
  ch.phis.set(v, next)
  return next
}

function chainTangent(e: Engine, wid: WireId, v: number, n: number): number {
  const ch = e.chains.get(wid)!
  const seg = Math.atan2(ch.pts[n]!.y - ch.pts[v]!.y, ch.pts[n]!.x - ch.pts[v]!.x)
  const bind = ch.binds.find((b) => b.idx === v)
  if (bind !== undefined) {
    const b = e.bodies.get(bind.body)!
    const a = b.localAnchor.get(bind.key)!
    return Math.atan2(a.y, a.x) + b.theta
  }
  if (ch.adj[v]!.length === 2) {
    const other = ch.adj[v]!.find((x) => x !== n)!
    return Math.atan2(ch.pts[n]!.y - ch.pts[other]!.y, ch.pts[n]!.x - ch.pts[other]!.x)
  }
  if (ch.adj[v]!.length >= 3) {
    const phi = junctionPhi(ch, v)
    const axisSide = Math.abs(wrap(phi - seg)) <= Math.PI / 2 ? phi : phi + Math.PI
    const wgt = Math.abs(Math.cos(seg - phi))
    const t = seg + wrap(axisSide - seg) * wgt
    // Hobby no-loop clamp against the chord
    const MAXDEV = Math.PI / 2 - 0.15
    return seg + Math.max(-MAXDEV, Math.min(MAXDEV, wrap(t - seg)))
  }
  return seg
}

/** Every drawable chain segment (slot-incident segments are boundary exits,
    emitted by boundaryExits instead). Synthesized LegEnds carry real
    (body, key) at bind terminals and homed bodies so endpoint-level gestures
    (drag-join) keep working; interior points get wire-local ids. */
export function computeLegs(e: Engine): LegGeom[] {
  const out: LegGeom[] = []
  for (const [wid, ch] of e.chains) {
    const slotIdx = new Set(ch.slots.map((s) => s.idx))
    const endOf = (idx: number): { body: string; key: string | null } => {
      const bind = ch.binds.find((b) => b.idx === idx)
      if (bind !== undefined) return { body: bind.body, key: bind.key }
      const hm = ch.homed.find((h) => h.idx === idx)
      if (hm !== undefined) return { body: hm.bodyId, key: null }
      return { body: `w:${wid}:${idx}`, key: null }
    }
    // terminal endpoints are DERIVED from their owning bodies at draw time
    // — never read from the chain, so a drawn wire cannot float off its
    // node no matter what the physics/pin ordering did this tick: the
    // attachment IS the disc-edge point of the body being painted
    const drawnAt = (idx: number): Vec2 => {
      const bind = ch.binds.find((b) => b.idx === idx)
      if (bind !== undefined) return worldBindAnchor(e.bodies.get(bind.body)!, bind.key)
      const hm = ch.homed.find((h) => h.idx === idx)
      if (hm !== undefined) return e.bodies.get(hm.bodyId)!.pos
      return ch.pts[idx]!
    }
    for (let v = 0; v < ch.pts.length; v++) {
      for (const n of ch.adj[v]!) {
        if (n <= v) continue
        if (slotIdx.has(v) || slotIdx.has(n)) continue
        out.push({
          leg: { wid, from: endOf(v), to: endOf(n) },
          pa: drawnAt(v),
          ta: chainTangent(e, wid, v, n),
          pb: drawnAt(n),
          tb: chainTangent(e, wid, n, v),
        })
      }
    }
  }
  return out
}

/** Hobby-spline path for every non-boundary, non-stub segment. */
export function legPaths(e: Engine): { wid: WireId; path: WirePath }[] {
  return computeLegs(e).map((g) => ({ wid: g.leg.wid, path: hobbyBezier(g.pa, g.ta, g.pb, g.tb) }))
}

/** One frame exit per boundary wire: the chain's slot-incident segment, drawn
    to the wire's canonical perimeter slot (fixed in boundary order, clockwise
    from the frame pip); the exit tangent at the frame is the slot normal. */
export function boundaryExits(e: Engine): BoundaryExit[] {
  const fbb = frameBounds(e)
  if (fbb === null) return []
  const slots = frameSlots(fbb, e.boundary.length)
  const out: BoundaryExit[] = []
  for (const [wid, ch] of e.chains) {
    for (const s of ch.slots) {
      const slot = slots[s.slot]!
      const nbr = ch.adj[s.idx]![0]
      if (nbr === undefined) continue
      const p = ch.pts[nbr]!
      const ta = chainTangent(e, wid, nbr, s.idx)
      out.push({ wid, path: hobbyBezier(p, ta, slot.point, slot.normal + Math.PI), tick: { center: slot.point, angle: slot.normal + Math.PI / 2 } })
    }
  }
  return out
}

/** Existential dots: a dangling wire end is its own body (USER LAW — the
    loose end IS the first-order ∃, homed at the wire's scope); a bare wire
    (no endpoints) is a dot alone. */
export function existentialStubs(e: Engine): ExStub[] {
  const out: ExStub[] = []
  const chainHomed = new Set<string>()
  for (const [wid, ch] of e.chains) {
    for (const hm of ch.homed) {
      chainHomed.add(hm.bodyId)
      const b = e.bodies.get(hm.bodyId)!
      out.push({ wid, from: b.pos, to: b.pos, dot: b.pos })
    }
  }
  for (const b of e.bodies.values()) {
    if (b.kind === 'junction' && !chainHomed.has(b.id) && b.id.startsWith('j:')) {
      out.push({ wid: b.id.slice(2), from: b.pos, to: b.pos, dot: b.pos })
    }
  }
  return out
}

/** The world anchor a wire meets a node at (the disc-edge attachment) —
    re-exported convenience for endpoint-level consumers. */
export function bindAnchor(e: Engine, body: string, key: string): Vec2 {
  return worldBindAnchor(e.bodies.get(body)!, key)
}
