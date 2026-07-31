import type { Vec2 } from '../vec'
import type { Bounds, Disc, HugArc } from './freespace'
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
    curve LEAVES it (null = natural end at the raw endpoint). */
export type CurveBC = { readonly p: Vec2; readonly n: Vec2 } | null

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

export type Cubic = { a: Vec2; c1: Vec2; c2: Vec2; b: Vec2 }

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

export function sampleCubics(cubics: readonly Cubic[]): Vec2[] {
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

/** Max hug angle one Hobby piece may span. The interior anchors exist ONLY to
    keep the drawn curve on the route's side of the hugged disc — never to
    trace the arc — and one tangent-clamped piece cannot reach the disc's far
    side while its subtended angle is under π; π/2 takes that bound with a 2×
    margin. At π/2 a cubic with tangential ends deviates from the circular arc
    by ~3·10⁻⁴·r (the classical quarter-circle cubic bound), so every span
    choice in [π/3, π] draws visually identical curves — a derived bound, not
    a tuning knob (executable: the span-insensitivity test). */
const HUG_SPAN = Math.PI / 2

/** The anchors of one hugging arc: its ENTRY and EXIT tangency points plus
    interior points on a fixed HUG_SPAN angular grid from the entry, each
    carrying the circle's EXACT tangent direction there (in the direction of
    travel). Anchoring the tangency points pins the curve at contact (the
    free entry/exit blends happen OUTSIDE the hug, so they cannot sag into the
    disc), and the grid rule makes the construction CONTINUOUS in the sweep: a
    new grid anchor appears precisely when the sweep crosses a grid multiple —
    i.e. exactly AT the exit anchor, already on the curve — and then separates
    smoothly. Equal-fraction placement would instead relocate every anchor
    whenever the count steps (a visible pop). */
function hugAnchors(h: HugArc): { p: Vec2; t: number }[] {
  const dir = h.sweep >= 0 ? 1 : -1
  const at = (a: number): { p: Vec2; t: number } => ({
    p: { x: h.c.x + h.r * Math.cos(a), y: h.c.y + h.r * Math.sin(a) },
    t: a + (Math.PI / 2) * dir,
  })
  const out: { p: Vec2; t: number }[] = [at(h.from)]
  const n = Math.floor(Math.abs(h.sweep) / HUG_SPAN + 1e-9)
  for (let k = 1; k <= n; k++) out.push(at(h.from + dir * HUG_SPAN * k))
  out.push(at(h.from + h.sweep))
  return out
}

/**
 * The drawn curve of one edge: the Hobby cubic chain anchored on the route's
 * CONTACT STRUCTURE (spec 2026-07-31). Anchors are the two terminals plus the
 * hug anchors of each contact arc; straight runs contribute nothing. A spline
 * through the route's sampled polyline reproduces the router's tangent-line-
 * plus-circular-arc geodesic — the rejected drafting look — so the samples
 * never reach the drawing. Clamped ends (port rim → outward normal, frame
 * slot → inward normal) fix the end tangents and REPLACE the route's
 * endpoints (the escape point is the anchor displaced along the clamp normal
 * — the same boundary datum — so keeping both would interpolate one datum
 * twice); every interior anchor carries its exact geometric tangent, so no
 * tangent is ever estimated from neighboring points; natural ends (junctions,
 * dots) take the chord toward the adjacent anchor. Deterministic, closed
 * form, stateless; the same samples are rendered and charged.
 */
export function edgeCurvePts(
  u: CurveBC,
  v: CurveBC,
  start: Vec2,
  end: Vec2,
  hugs: readonly HugArc[],
  clampLayer = 0,
): Vec2[] {
  return sampleCubics(edgeCurveCubics(u, v, start, end, hugs, clampLayer))
}

/** The edge's Hobby cubic chain itself — the renderer draws THESE as true
    Bézier path segments (sampled polylines are for energy and hit-testing;
    drawing them as line segments is visibly faceted). */
export function edgeCurveCubics(
  u: CurveBC,
  v: CurveBC,
  start: Vec2,
  end: Vec2,
  hugs: readonly HugArc[],
  clampLayer = 0,
): Cubic[] {
  const a0: Vec2 = u !== null ? { ...u.p } : { ...start }
  const a1: Vec2 = v !== null ? { ...v.p } : { ...end }
  // Interior anchors, dropping any that coincide with a terminal anchor (a
  // grazing contact at an endpoint — the terminal's clamp wins), and any
  // within `clampLayer` (= r*, the rod bend radius — USER rod ruling
  // 2026-07-24) of a CLAMPED terminal: a rod cannot conform to contact detail
  // inside its own bend scale, and a wire leaving a port immediately hugs its
  // own node's inflated disc, putting a tangency anchor with a perpendicular
  // tangent right next to the clamp — one boundary datum interpolated twice
  // (measured: a 0.54-radius curl at the port of a forced U-turn).
  const inLayer = (bc: CurveBC, p: Vec2): boolean =>
    bc !== null && Math.hypot(p.x - bc.p.x, p.y - bc.p.y) < clampLayer
  const interior = hugs.flatMap(hugAnchors).filter(
    (a) =>
      Math.hypot(a.p.x - a0.x, a.p.y - a0.y) >= 1e-9 &&
      Math.hypot(a.p.x - a1.x, a.p.y - a1.y) >= 1e-9 &&
      !inLayer(u, a.p) && !inLayer(v, a.p),
  )
  const Q: { p: Vec2; t: number | null }[] = [{ p: a0, t: null }]
  for (const a of interior) {
    const last = Q[Q.length - 1]!
    if (Math.hypot(a.p.x - last.p.x, a.p.y - last.p.y) < 1e-9) continue
    Q.push({ p: a.p, t: a.t })
  }
  if (Math.hypot(a1.x - Q[Q.length - 1]!.p.x, a1.y - Q[Q.length - 1]!.p.y) >= 1e-9) Q.push({ p: a1, t: null })
  if (Q.length < 2) return []
  const m = Q.length - 1
  const chord = (i: number, j: number): number => Math.atan2(Q[j]!.p.y - Q[i]!.p.y, Q[j]!.p.x - Q[i]!.p.x)
  const uAng = u !== null ? Math.atan2(u.n.y, u.n.x) : chord(0, 1)
  const vAng = v !== null ? Math.atan2(v.n.y, v.n.x) : chord(m - 1, m) + Math.PI
  const cubics: Cubic[] = []
  for (let i = 0; i + 1 < Q.length; i++) {
    const ta = i === 0 ? uAng : Q[i]!.t!
    const tb = i + 1 === m ? vAng : Q[i + 1]!.t! + Math.PI
    cubics.push(hobbySeg(Q[i]!.p, ta, Q[i + 1]!.p, tb))
  }
  return cubics
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
