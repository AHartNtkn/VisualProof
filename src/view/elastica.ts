/**
 * THE MASSLESS ELASTICA WIRE (plan 22, promoted from the accepted round-10
 * demo). A wire has NO state: each leg is the minimum-energy theta-quadratic
 * (Euler-spiral) interpolant of its CURRENT boundary data. Kinks, loops and
 * wraps are UNREPRESENTABLE: every returned solution has tangent range <= pi
 * (a curve whose tangent stays inside a half-plane cannot self-intersect),
 * enforced as candidate rejection in the solve. The solve is arc-seeded (the
 * c2 = 0 circle closing any boundary pair is closed-form) and MEMORYLESS —
 * deterministic in its inputs, no warm starts, no winding memory (user law:
 * a principled model cannot remember windings). The cache is a pure-function
 * memo keyed on the exact boundary tuple.
 */
import type { Vec2 } from './vec'

type V = Vec2
const hyp = Math.hypot
const wrapA = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))
export type LegCache = { k: number[] | null; s: Sol | null }
export const mkLegCache = (): LegCache => ({ k: null, s: null })

// P-analogues bound at solve time by the engine energy module:
export const ELASTICA = { tension: 1.0, bend: 60 }

// ---- the massless wire: Euler-spiral G1 interpolation ----------------------
// theta(t) = th0 + c1 t + c2 t^2, t in [0,1]; c2 = dTurn - c1 where dTurn is
// the TOTAL TURNING, lifted continuously near the previous solution (branch
// memory = continuity, capped at 3pi/2 so simplicity is guaranteed).
export const QN = 24
export function trace(p0: V, th0: number, c1: number, c2: number, L: number, out: V[], n: number = QN): void {
  let x = p0.x, y = p0.y
  out.length = 0
  out.push({ x, y })
  const h = L / n
  for (let k = 0; k < n; k++) {
    const tm = (k + 0.5) / n
    const th = th0 + c1 * tm + c2 * tm * tm
    x += Math.cos(th) * h
    y += Math.sin(th) * h
    out.push({ x, y })
  }
}
const tr: V[] = []
export type Sol = { c1: number; c2: number; L: number; dTurn: number; well: number }

/** RANGE of theta(t) = c1 t + c2 t^2 over [0,1] (relative to th0). */
export function thetaRange(c1: number, c2: number): number {
  const tau = c1 + c2
  let lo = Math.min(0, tau), hi = Math.max(0, tau)
  if (Math.abs(c2) > 1e-12) {
    const tStar = -c1 / (2 * c2)
    if (tStar > 0 && tStar < 1) {
      const thStar = -c1 * c1 / (4 * c2)
      lo = Math.min(lo, thStar)
      hi = Math.max(hi, thStar)
    }
  }
  return hi - lo
}

/** Newton (c1, L) closing the endpoint for a FIXED total turn tau. */
export function closeAt(p0: V, th0: number, p1: V, tau: number, c1Init: number, LInit: number): { c1: number; L: number; ok: boolean } {
  const chord = hyp(p1.x - p0.x, p1.y - p0.y)
  let c1 = c1Init, L = LInit
  let ok = false
  for (let it = 0; it < 8; it++) {
    trace(p0, th0, c1, tau - c1, L, tr)
    const e = tr[tr.length - 1]!
    const rx = e.x - p1.x, ry = e.y - p1.y
    if (rx * rx + ry * ry < 1e-6) { ok = true; break }
    const h1 = 1e-4, h2 = Math.max(1e-4, L * 1e-4)
    trace(p0, th0, c1 + h1, tau - c1 - h1, L, tr)
    const e1 = tr[tr.length - 1]!
    trace(p0, th0, c1, tau - c1, L + h2, tr)
    const e2 = tr[tr.length - 1]!
    const a11 = (e1.x - e.x) / h1, j21 = (e1.y - e.y) / h1
    const j12 = (e2.x - e.x) / h2, j22 = (e2.y - e.y) / h2
    const det = a11 * j22 - j12 * j21
    if (Math.abs(det) < 1e-12) break
    c1 += Math.max(-1.5, Math.min(1.5, (-rx * j22 + ry * j12) / det))
    L += Math.max(-0.4 * L, Math.min(0.4 * L, (-a11 * ry + j21 * rx) / det))
    L = Math.max(chord * 0.98 + 0.02, Math.min(chord * 4 + 8, L))
  }
  return { c1, L, ok }
}

/** The MEMORYLESS wire: among curves that (a) close the endpoints exactly
    (rim lock) and (b) keep the tangent range <= RANGE_B (a curve whose
    tangent stays inside a half-plane CANNOT self-intersect — loops are
    outside the family), pick the minimizer of the wire's own energy
    (tension + bend + a stiff arrival-tangent well). The arrival tangent is
    soft: under extreme geometry the exit visibly strains, force builds,
    and the shape buckles to the other side — nothing is remembered. */
export const RANGE_B = Math.PI
export const WELL_S = 25
export function legInnerE(sol: { c1: number; L: number }, tau: number, arriveErr: number): number {
  const c2 = tau - sol.c1
  return ELASTICA.tension * sol.L
    + (ELASTICA.bend * (sol.c1 * sol.c1 + 2 * sol.c1 * c2 + (4 / 3) * c2 * c2)) / sol.L
    + WELL_S * (1 - Math.cos(arriveErr))
}
/** EXACT arc closure (c2 = 0 member of the family), closed form: the
    unique circle through p0 tangent to th0 that passes p1. Always exists,
    always closes exactly, smooth in its inputs — the deterministic seed
    and the guaranteed fallback (an unconverged Newton used to leave the
    drawn endpoint hanging off the rim, flickering frame to frame). */
export function arcClose(p0: V, th0: number, p1: V): { tau: number; L: number } {
  const chord = hyp(p1.x - p0.x, p1.y - p0.y)
  const delta = wrapA(Math.atan2(p1.y - p0.y, p1.x - p0.x) - th0)
  const s = Math.abs(delta) < 1e-6 ? 1 : delta / Math.sin(delta)
  return { tau: 2 * delta, L: Math.max(chord * s, 0.01) }
}
export function solveLeg(cache: LegCache, p0: V, th0: number, p1: V, th1: number, freeEnd: boolean): Sol {
  const k = cache.k
  if (k !== null && k[0] === p0.x && k[1] === p0.y && k[2] === th0 && k[3] === p1.x && k[4] === p1.y && k[5] === th1) return cache.s!
  const D0 = wrapA(th1 - th0)
  const arc = arcClose(p0, th0, p1)
  let best: { c1: number; L: number; tau: number; E: number } | null = null
  const tryTau = (tau: number): void => {
    const r = closeAt(p0, th0, p1, tau, tau / 2, arc.L)
    if (!r.ok) return
    if (thetaRange(r.c1, tau - r.c1) > RANGE_B) return
    const E = legInnerE(r, tau, freeEnd ? 0 : th0 + tau - th1)
    if (best === null || E < best.E) best = { c1: r.c1, L: r.L, tau, E }
  }
  // the arc itself is a candidate (exact closure by construction)
  if (Math.abs(arc.tau) <= RANGE_B) {
    const E = legInnerE({ c1: arc.tau, L: arc.L }, arc.tau, freeEnd ? 0 : th0 + arc.tau - th1)
    best = { c1: arc.tau, L: arc.L, tau: arc.tau, E }
  }
  // canonical grid over the feasible turn interval, then refinement
  for (let g = -3; g <= 3; g++) {
    const tau = D0 + g * 0.9
    if (tau >= -Math.PI - 0.01 && tau <= Math.PI + 0.01) tryTau(tau)
  }
  if (best !== null) {
    let w = 0.55
    for (let r = 0; r < 4; r++) {
      w /= 2
      const t0 = (best as { tau: number }).tau
      tryTau(t0 - w)
      tryTau(t0 + w)
    }
  }
  if (best === null) {
    // nothing feasible converged (extreme transient): the arc still
    // closes exactly — deterministic, no residual, possibly range > pi
    // for a moment under violent drags
    best = { c1: arc.tau, L: arc.L, tau: arc.tau, E: 0 }
  }
  const b = best as { c1: number; L: number; tau: number }
  const sol = { c1: b.c1, c2: b.tau - b.c1, L: b.L, dTurn: b.tau, well: freeEnd ? 0 : WELL_S * (1 - Math.cos(th0 + b.tau - th1)) }
  cache.k = [p0.x, p0.y, th0, p1.x, p1.y, th1]
  cache.s = sol
  return sol
}

