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
// The leg solve is a PURE function of its exact boundary tuple (p0, th0, p1, th1);
// the cache is a small FIFO ring of recent (tuple → solution) entries. A strict
// gated step probes a DOF away from its base and returns to that base after every
// rejected trial (backtracking + long-shot), so the base tuple recurs many times
// within one sweep; a single slot is overwritten by the intervening trial and
// re-solves the base each return. The ring holds enough recent tuples that the base
// stays resident across one gate's probes. Reuse is by EXACT tuple equality, so a
// returned solution always matches its own inputs — a changed tuple simply misses
// and solves fresh; a stale shape can never be returned (the exact-key match IS the
// invalidation). Output is therefore bit-identical to the single-slot memo.
const CACHE_N = 16
export type LegCache = { keys: (number[] | null)[]; sols: (Sol | null)[]; next: number }
export const mkLegCache = (): LegCache => ({ keys: new Array(CACHE_N).fill(null), sols: new Array(CACHE_N).fill(null), next: 0 })
// Cache control + instrumentation. `enabled` (default on) exists ONLY so a law test
// can settle a fixture with the memo off and confirm the layout is bit-identical to
// settling with it on — the executable proof that the memo is output-neutral (a hit
// returns a solution whose stored key exactly equals the query, which by the
// memoryless purity of the solve equals a fresh solve). `calls`/`hits` are the
// hit-rate counters read by the measure-sweep perf gate.
export const legCache = { enabled: true, calls: 0, hits: 0 }

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

/** Newton (c1, L) closing the endpoint for a FIXED total turn tau. The 2×2
    Jacobian of the endpoint w.r.t. (c1, L) is ANALYTIC, accumulated in the SAME
    quadrature pass that computes the endpoint (no finite-difference perturbation
    traces): with θ(t) = th0 + c1·t + (tau−c1)·t² the c1-sensitivity of the heading
    is ∂θ/∂c1 = t(1−t), and since θ is L-independent the endpoint's L-sensitivity is
    just (endpoint − p0)/L. One pass replaces the former three (endpoint + two
    perturbed), and the exact derivative sharpens Newton — same root, fewer traces. */
export function closeAt(p0: V, th0: number, p1: V, tau: number, c1Init: number, LInit: number): { c1: number; L: number; ok: boolean } {
  const chord = hyp(p1.x - p0.x, p1.y - p0.y)
  let c1 = c1Init, L = LInit
  let ok = false
  for (let it = 0; it < 8; it++) {
    // endpoint (midpoint quadrature, matching `trace`) + analytic ∂endpoint/∂c1
    const c2 = tau - c1
    let x = p0.x, y = p0.y, dxc = 0, dyc = 0
    const h = L / QN
    for (let k = 0; k < QN; k++) {
      const tm = (k + 0.5) / QN
      const th = th0 + c1 * tm + c2 * tm * tm
      const ct = Math.cos(th), st = Math.sin(th)
      x += ct * h; y += st * h
      const wgt = tm * (1 - tm) // ∂θ/∂c1 at fixed tau
      dxc += -st * wgt * h; dyc += ct * wgt * h
    }
    const rx = x - p1.x, ry = y - p1.y
    if (rx * rx + ry * ry < 1e-6) { ok = true; break }
    const a11 = dxc, j21 = dyc
    const j12 = (x - p0.x) / L, j22 = (y - p0.y) / L
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
/** Regularize the fallback turning just short of a full loop (tau → 2pi is the
    L → infinity singularity of arcClose): 2·(pi − DELTA_EPS). Beyond this the
    length is essentially unbounded; below it the length grows steeply but
    finitely, which is what preserves the gradient across the blind cone. */
const DELTA_EPS = 0.05
export function solveLeg(cache: LegCache, p0: V, th0: number, p1: V, th1: number, freeEnd: boolean): Sol {
  legCache.calls++
  const { keys, sols } = cache
  if (legCache.enabled) for (let i = 0; i < CACHE_N; i++) {
    const k = keys[i]
    if (k != null && k[0] === p0.x && k[1] === p0.y && k[2] === th0 && k[3] === p1.x && k[4] === p1.y && k[5] === th1) {
      legCache.hits++
      return sols[i]!
    }
  }
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
  // UNIFORM scan over the WHOLE feasible turn interval [−π, π] for EVERY leg,
  // then refinement. The arrival condition is soft or absent for the two leg
  // kinds that need this: a hub leg's arrival angle is a RELAXING DOF (finite
  // spread energy), and a free-end leg's th1 is a dummy — so a D0 = wrapA(th1 −
  // th0)-centered scan can EXCLUDE the tau ≈ ±π solution a port facing away from
  // its target needs, and coordinate descent cannot walk the soft angle and tau
  // jointly past the gap. A port→port leg's well merely makes distant-tau
  // candidates expensive, which the energy selection already discards — so one
  // policy, the whole family always in view. The tau = +π/−π tie for a
  // directly-behind target is broken by scan order (−π first): the memoryless
  // law depends on this determinism.
  for (let k2 = -4; k2 <= 4; k2++) tryTau((k2 * Math.PI) / 4)
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
    // NO representable candidate: the target is in the blind cone behind the
    // port (a > pi turn is needed — no range ≤ π θ-quadratic closes it). Take
    // the exact arc, but regularize ONLY the tau → 2pi singularity so the length
    // stays finite yet STEEPLY, MONOTONICALLY increasing with blind-cone depth:
    // the leg must remain energetically REPULSIVE in proportion to how deep its
    // target sits, or a movable hub/tip has no gradient to migrate OUT of the
    // cone (and the node no torque to rotate to face it). Capping the LENGTH
    // instead flattens that gradient and lets the leg REST in the cone — the
    // dead-zone-from-clamping failure. Only the last sliver (delta within
    // DELTA_EPS of π) is bounded, where the length is already enormous.
    const delta = wrapA(Math.atan2(p1.y - p0.y, p1.x - p0.x) - th0)
    const dc = Math.abs(delta) > Math.PI - DELTA_EPS ? Math.sign(delta || 1) * (Math.PI - DELTA_EPS) : delta
    const s = Math.abs(dc) < 1e-6 ? 1 : dc / Math.sin(dc)
    const L = Math.max(hyp(p1.x - p0.x, p1.y - p0.y) * s, 0.01)
    best = { c1: 2 * dc, L, tau: 2 * dc, E: 0 }
  }
  const b = best as { c1: number; L: number; tau: number }
  const sol = { c1: b.c1, c2: b.tau - b.c1, L: b.L, dTurn: b.tau, well: freeEnd ? 0 : WELL_S * (1 - Math.cos(th0 + b.tau - th1)) }
  const slot = cache.next
  const ex = keys[slot]
  if (ex == null) keys[slot] = [p0.x, p0.y, th0, p1.x, p1.y, th1]
  else { ex[0] = p0.x; ex[1] = p0.y; ex[2] = th0; ex[3] = p1.x; ex[4] = p1.y; ex[5] = th1 }
  sols[slot] = sol
  cache.next = (slot + 1) % CACHE_N
  return sol
}

