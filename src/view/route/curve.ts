import type { Vec2 } from '../vec'
import type { Bounds, Disc } from './freespace'
import { POLY_K, segSoftCost } from './freespace'

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

const perp = (a: Vec2): Vec2 => ({ x: -a.y, y: a.x })

/**
 * The rod boundary layer at a clamped end, in closed form: the arc of radius
 * ρ tangent to the clamp direction `n` at `A`, followed until its tangent
 * line aims at `P` (the first corridor point). Both circle sides are tried;
 * the smaller sweep wins (deterministic, ties → left). Returns [A, …arc
 * samples…, touch point]; empty sweep (P straight ahead) returns just [A].
 * Degenerate P inside both circles falls back to the straight leave.
 */
function clampArc(A: Vec2, n: Vec2, P: Vec2, rho: number): Vec2[] {
  let best: { sweep: number; C: Vec2; a0: number; o: number; psi: number } | null = null
  for (const side of [1, -1] as const) {
    const C = { x: A.x + rho * side * perp(n).x, y: A.y + rho * side * perp(n).y }
    const dx = P.x - C.x, dy = P.y - C.y
    const d = Math.hypot(dx, dy)
    if (d < rho * (1 + 1e-9)) continue
    const a0 = Math.atan2(A.y - C.y, A.x - C.x)
    // orientation: the tangent at A must equal +n
    const o = -Math.sin(a0) * n.x + Math.cos(a0) * n.y > 0 ? 1 : -1
    const phi = Math.atan2(dy, dx)
    const delta = Math.acos(Math.min(1, rho / d))
    for (const sgn of [1, -1] as const) {
      const psi = phi + sgn * delta
      // leaving tangent at the touch point must continue the orientation AND head toward P
      const tx = -Math.sin(psi) * o, ty = Math.cos(psi) * o
      const touch = { x: C.x + rho * Math.cos(psi), y: C.y + rho * Math.sin(psi) }
      if (tx * (P.x - touch.x) + ty * (P.y - touch.y) <= 0) continue
      let sweep = o * (psi - a0)
      sweep = ((sweep % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI)
      if (best === null || sweep < best.sweep) best = { sweep, C, a0, o, psi }
    }
  }
  if (best === null) return [A]
  const { sweep, C, a0, o } = best
  if (sweep < 1e-6) return [A]
  const N = Math.max(2, Math.ceil(sweep / (Math.PI / 8)))
  const out: Vec2[] = [A]
  for (let k = 1; k <= N; k++) {
    const t = a0 + o * sweep * (k / N)
    out.push({ x: C.x + rho * Math.cos(t), y: C.y + rho * Math.sin(t) })
  }
  return out
}

/**
 * The drawn curve of one edge: closed-form rod geometry over the routed
 * corridor. `routePts` are the router's waypoints (escape-level endpoints
 * included). At a clamped end the curve is the r*-arc tangent to the clamp
 * normal (the rod boundary layer — within r* of a clamped end a rod cannot
 * conform to corridor detail, so corridor points inside that zone drop),
 * leaving tangentially toward the first corridor point; the corridor
 * polyline follows (its corners live at the disc-polygon resolution, gentle
 * by construction); the far end mirrors. Natural ends (junctions, dots) join
 * the corridor directly. Deterministic, closed form, stateless — the same
 * construction is rendered and charged (drawn = charged, one law).
 */
export function edgeCurvePts(
  u: CurveBC,
  v: CurveBC,
  routePts: readonly Vec2[],
  space: { readonly discs: readonly Disc[]; readonly bounds: Bounds | null } | null = null,
  beta = 0,
): Vec2[] {
  void space
  const core: Vec2[] = routePts.map((p) => ({ ...p }))
  const rStar = Math.sqrt(beta)
  const zone = (bc: CurveBC): number =>
    bc !== null && bc.ownDisc != null ? Math.max((2 * Math.PI * bc.ownDisc.r) / POLY_K, rStar) : rStar
  let lead = 0
  const zoneU = zone(u)
  while (u !== null && lead < core.length && Math.hypot(core[lead]!.x - u.p.x, core[lead]!.y - u.p.y) < zoneU) lead++
  let trail = core.length - 1
  const zoneV = zone(v)
  while (v !== null && trail >= lead && Math.hypot(core[trail]!.x - v.p.x, core[trail]!.y - v.p.y) < zoneV) trail--
  const mid = core.slice(lead, trail + 1)
  // arc targets: the first surviving corridor point; with the corridor fully
  // consumed, aim at the far end's own boundary-layer knee (its virtual
  // escape) — the two arcs then join by their common tangent line
  const uTarget = mid.length > 0 ? mid[0]! : v !== null ? { x: v.p.x + v.n.x * rStar, y: v.p.y + v.n.y * rStar } : core[core.length - 1]!
  const vTarget = mid.length > 0 ? mid[mid.length - 1]! : u !== null ? { x: u.p.x + u.n.x * rStar, y: u.p.y + u.n.y * rStar } : core[0]!
  const head = u !== null && rStar > 0 ? clampArc(u.p, u.n, uTarget, rStar) : [core[0] ?? (u !== null ? u.p : { x: 0, y: 0 })]
  const tail = v !== null && rStar > 0 ? clampArc(v.p, v.n, vTarget, rStar).reverse() : [core[core.length - 1] ?? (v !== null ? v.p : { x: 0, y: 0 })]
  if (u !== null && rStar <= 0) head[0] = { ...u.p }
  if (v !== null && rStar <= 0) tail[tail.length - 1] = { ...v.p }
  const way = [...head, ...mid, ...tail]
  // drop degenerate duplicates
  const out: Vec2[] = []
  for (const p of way) {
    const last = out[out.length - 1]
    if (last !== undefined && Math.hypot(p.x - last.x, p.y - last.y) < 1e-9) continue
    out.push(p)
  }
  return out
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
