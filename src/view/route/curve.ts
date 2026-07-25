import type { Vec2 } from '../vec'
import type { Bounds, Disc } from './freespace'
import { segSoftCost } from './freespace'

/**
 * THE DRAWN CURVE + ROD ENERGY (USER ruling 2026-07-24: "the minimal energy
 * curves should be gentle... the energy function for the curve shapes is
 * simply wrong — rethink it from first principles").
 *
 * First principles: a wire is a thin elastic rod (the standing physical-wire
 * law). Its shape energy is the classical functional
 *
 *     E[curve] = ∫ (α + β·κ(s)²) ds        (α = 1: unit tension)
 *
 * A total-turn charge is placement-invariant (a sharp corner and a wide arc
 * with the same net turn cost the same), so its minimizers are exactly
 * straight polylines with point corners — the observed defect. κ² breaks the
 * invariance: for a fixed net turn Δθ over arclength L the bending cost is
 * β·Δθ²/L, DECREASING in L, so turning spreads out and the minimizers are
 * gentle. The balance defines the characteristic bend radius r* = √(β/α);
 * bends flatter than r* are nearly free, tighter ones increasingly dear. β is
 * DERIVED, not tuned: r* = the node-disc scale (bends happen at the scale of
 * the objects they route around), so β = r*².
 *
 * The drawn curve of a routed edge is a DETERMINISTIC cubic Hermite spline
 * through the route's waypoints: clamped tangents where the edge meets a
 * fixed anchor (port rim → outward normal; frame slot → inward normal —
 * perpendicular meetings by energy, not construction), free (natural) ends at
 * junctions and dots. No curve state exists — edges stay incidences only;
 * the same construction is rendered and charged (drawn = charged, one law).
 */

/** Terminal boundary condition: fixed anchor point + the unit direction the
    curve LEAVES it (null = natural end at the raw endpoint). `ownDisc` is the
    terminal body's inflated obstacle disc: route waypoints hugging it are
    escape-routing artifacts inside the clamp's ownership zone and are dropped
    from the curve's waypoints (the clamp + rod energy own the shape there). */
export type CurveBC = { readonly p: Vec2; readonly n: Vec2; readonly ownDisc?: Disc | null } | null

const sub = (a: Vec2, b: Vec2): Vec2 => ({ x: a.x - b.x, y: a.y - b.y })
const len = (a: Vec2): number => Math.hypot(a.x, a.y)

const wrapA = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

/**
 * THE CURVE FAMILY (USER LAW, 2026-07-24): wires are drawn as HOBBY cubic
 * splines — the round-8 render-lab family ("good to integrate"), ported
 * faithfully from render-lab8/round9-spline (hobbyRho mock-curvature
 * velocity, cubic control arms |rho|·d/3). Spiral-curvature representations
 * (Euler spirals, clothoids, θ-polynomials) are BANNED — the plan-22
 * elastica legs were an approximation of this family that introduced
 * exactly that banned class. Arc-line-arc constant-curvature chains are
 * likewise rejected (mechanical drafting look). The cubics are sampled for
 * both painting and energy — what is drawn IS what is charged.
 */
function hobbyRho(t: number, f: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  return (2 + a * (Math.sin(t) - b * Math.sin(f)) * (Math.sin(f) - b * Math.sin(t)) * (Math.cos(t) - Math.cos(f))) /
    (1 + (1 - c) * Math.cos(t) + c * Math.cos(f))
}

type Cubic = { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }

/** One Hobby segment: pa → pb with OUTWARD tangent angles at both ends
    (start: forward travel; end: forward + π, or the far rim's port normal). */
function hobbySeg(pa: Vec2, ta: number, pb: Vec2, tb: number): Cubic {
  const chord = Math.atan2(pb.y - pa.y, pb.x - pa.x)
  const d = Math.hypot(pb.x - pa.x, pb.y - pa.y)
  const th = wrapA(ta - chord), ph = wrapA(chord - (tb + Math.PI))
  const ra = (Math.abs(hobbyRho(th, ph)) * d) / 3
  const rb = (Math.abs(hobbyRho(ph, th)) * d) / 3
  return {
    a: pa,
    c1: { x: pa.x + Math.cos(ta) * ra, y: pa.y + Math.sin(ta) * ra },
    c2: { x: pb.x + Math.cos(tb) * rb, y: pb.y + Math.sin(tb) * rb },
    b: pb,
  }
}

/** Samples per cubic (the lab's SUB): painting and energy share them. */
const SUB = 7

function sampleCubics(cubics: readonly Cubic[]): Vec2[] {
  const out: Vec2[] = []
  for (const c of cubics) {
    const from = out.length === 0 ? 0 : 1
    for (let k = from; k <= SUB; k++) {
      const t = k / SUB
      const u = 1 - t
      const p = {
        x: u * u * u * c.a.x + 3 * u * u * t * c.c1.x + 3 * u * t * t * c.c2.x + t * t * t * c.b.x,
        y: u * u * u * c.a.y + 3 * u * u * t * c.c1.y + 3 * u * t * t * c.c2.y + t * t * t * c.b.y,
      }
      const last = out[out.length - 1]
      if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
      out.push(p)
    }
  }
  return out
}

/**
 * The drawn curve of one edge: the Hobby cubic chain through the routed
 * corridor waypoints. Clamped ends (port rim → outward normal, frame slot →
 * inward normal) fix the end tangents; interior anchors take Catmull-Rom
 * forward directions; natural ends (junctions, dots) take the chord. Route
 * corridor points inside a clamped end's neighborhood (max of one disc
 * polygon step and r*) are routing artifacts of the escape point and drop —
 * the clamped cubic owns that approach. Deterministic, closed form,
 * stateless; the same samples are rendered and charged.
 */
export function edgeCurvePts(
  u: CurveBC,
  v: CurveBC,
  routePts: readonly Vec2[],
  space: { readonly discs: readonly Disc[]; readonly bounds: Bounds | null } | null = null,
  beta = 0,
): Vec2[] {
  void space
  void beta
  const core: Vec2[] = routePts.map((p) => ({ ...p }))
  const pts: Vec2[] = [
    ...(u !== null ? [{ ...u.p }] : []),
    ...core,
    ...(v !== null ? [{ ...v.p }] : []),
  ]
  // dedupe
  const Q: Vec2[] = []
  for (const p of pts) {
    const last = Q[Q.length - 1]
    if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
    Q.push(p)
  }
  if (Q.length < 2) return Q
  const m = Q.length - 1
  const catmull = (i: number): number => {
    const a = Q[Math.max(0, i - 1)]!, b = Q[Math.min(m, i + 1)]!
    return Math.atan2(b.y - a.y, b.x - a.x)
  }
  // FORWARD travel direction at each anchor (the lab's fwd); clamped ends use
  // their normals as OUTWARD tangents directly
  const fwd: number[] = Q.map((_, i) => catmull(i))
  const uAng = u !== null ? Math.atan2(u.n.y, u.n.x) : fwd[0]!
  const vAng = v !== null ? Math.atan2(v.n.y, v.n.x) : fwd[m]! + Math.PI
  const cubics: Cubic[] = []
  for (let i = 0; i + 1 < Q.length; i++) {
    const ta = i === 0 ? uAng : fwd[i]!
    const tb = i + 1 === m ? vAng : fwd[i + 1]! + Math.PI
    cubics.push(hobbySeg(Q[i]!, ta, Q[i + 1]!, tb))
  }
  return sampleCubics(cubics)
}

/**
 * Discrete rod energy of a sampled curve: Σ soft segment cost (length +
 * through-disc + out-of-frame surcharges — THE soft metric) + β·Σ Δθᵢ²/Δs̄ᵢ
 * (the discrete ∫κ²ds). A point corner concentrates Δθ over vanishing Δs̄ and
 * diverges — corners cannot survive at a minimum.
 */
export function rodCost(
  pts: readonly Vec2[],
  space: { readonly discs: readonly Disc[]; readonly bounds: Bounds | null },
  beta: number,
): number {
  let E = 0
  for (let i = 0; i + 1 < pts.length; i++) E += segSoftCost(pts[i]!, pts[i + 1]!, space)
  for (let i = 1; i + 1 < pts.length; i++) {
    const a = sub(pts[i]!, pts[i - 1]!)
    const b = sub(pts[i + 1]!, pts[i]!)
    const la = len(a), lb = len(b)
    if (la < 1e-12 || lb < 1e-12) continue
    const dot = Math.max(-1, Math.min(1, (a.x * b.x + a.y * b.y) / (la * lb)))
    const dth = Math.acos(dot)
    E += (beta * dth * dth) / ((la + lb) / 2)
  }
  return E
}
