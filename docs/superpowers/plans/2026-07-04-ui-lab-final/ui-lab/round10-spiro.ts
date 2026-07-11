/**
 * ROUND 10 — WIRES ARE MASSLESS ELASTICA (zero-DOF, loop-free by theorem).
 *
 * A wire has NO state. At every instant it is the unique minimum-bending
 * curve meeting its boundary conditions (leave port A along the normal,
 * arrive at port B along the normal): the Euler-spiral G1 interpolant,
 * theta(t) = th0 + c1 t + c2 t^2 over arc length. Kinks are unrepresentable
 * (theta continuous); loops are unrepresentable (monotone-curvature curves
 * self-cross only past ~2pi of turning; the solver lives on the minimal
 * branch, |turn| <= 3pi/2). The only DOF are bodies (pos + rotation),
 * junction hubs, and the dangle tip — driven by strict per-DOF descent of
 * ONE energy: tension·L + bend·∫k²ds (closed form) + node-clearance and
 * wire-separation line integrals (reciprocal: wires push and torque nodes).
 * Warm-started solving makes shapes follow bodies continuously — no snaps.
 */

type V = { x: number; y: number }
const hyp = Math.hypot
const wrapA = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

// ---- scene ------------------------------------------------------------------
type Disc = { id: string; pos: V; theta: number; r: number; ports: number[] }
const P = { tension: 1.0, bend: 60, clearSlope: 3.2, clearMargin: 5, sepSlope: 1.4, sepR: 5 }

const discs: Disc[] = [
  { id: 'plus', pos: { x: -70, y: -20 }, theta: 0.3, r: 16, ports: [0, 2.1, 4.2] },
  { id: 'times', pos: { x: 60, y: -55 }, theta: 1.2, r: 16, ports: [0, 2.1, 4.2] },
  { id: 'succ', pos: { x: 85, y: 45 }, theta: -0.8, r: 14, ports: [0, Math.PI] },
  { id: 'zero', pos: { x: -15, y: 70 }, theta: 0.5, r: 12, ports: [0] },
  { id: 'nat', pos: { x: -95, y: 70 }, theta: -0.4, r: 13, ports: [0, Math.PI] },
  { id: 'lt', pos: { x: 5, y: -95 }, theta: 1.9, r: 13, ports: [0, Math.PI] },
]

type End = { disc: number; port: number }
/** A leg runs port -> port, port -> hub, or port -> tip. Its SHAPE is not
    state — only the solver warm start lives here (branch continuity). */
type Leg = { a: End; b: End | 'hub' | 'tip'; cacheK: number[] | null; cacheS: Sol | null }
type Wire = { legs: Leg[]; hub: V | null; hubT: number[]; tip: V | null; tipT: number }

const wires: Wire[] = [
  { // 3-way plus/times/succ: three legs into a hub with a trunk axis
    legs: [
      { a: { disc: 0, port: 0 }, b: 'hub', cacheK: null, cacheS: null },
      { a: { disc: 1, port: 0 }, b: 'hub', cacheK: null, cacheS: null },
      { a: { disc: 2, port: 0 }, b: 'hub', cacheK: null, cacheS: null },
    ],
    hub: { x: 20, y: -10 }, hubT: [0.2 + Math.PI, 0.2, 1.7], tip: null, tipT: 0,
  },
  { legs: [{ a: { disc: 0, port: 1 }, b: { disc: 3, port: 0 }, cacheK: null, cacheS: null }], hub: null, hubT: [], tip: null, tipT: 0 },
  { legs: [{ a: { disc: 1, port: 1 }, b: { disc: 4, port: 0 }, cacheK: null, cacheS: null }], hub: null, hubT: [], tip: null, tipT: 0 },
  { legs: [{ a: { disc: 0, port: 2 }, b: { disc: 5, port: 0 }, cacheK: null, cacheS: null }], hub: null, hubT: [], tip: null, tipT: 0 },
  { legs: [{ a: { disc: 5, port: 1 }, b: { disc: 2, port: 1 }, cacheK: null, cacheS: null }], hub: null, hubT: [], tip: null, tipT: 0 },
  { legs: [{ a: { disc: 4, port: 1 }, b: 'tip', cacheK: null, cacheS: null }], hub: null, hubT: [], tip: { x: -130, y: 90 }, tipT: 2.6 },
]

function rim(end: End): { p: V; n: number } {
  const d = discs[end.disc]!
  const a = d.theta + d.ports[end.port]!
  return { p: { x: d.pos.x + Math.cos(a) * d.r, y: d.pos.y + Math.sin(a) * d.r }, n: a }
}

// ---- the massless wire: Euler-spiral G1 interpolation ----------------------
// theta(t) = th0 + c1 t + c2 t^2, t in [0,1]; c2 = dTurn - c1 where dTurn is
// the TOTAL TURNING, lifted continuously near the previous solution (branch
// memory = continuity, capped at 3pi/2 so simplicity is guaranteed).
const QN = 24
function trace(p0: V, th0: number, c1: number, c2: number, L: number, out: V[], n: number = QN): void {
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
type Sol = { c1: number; c2: number; L: number; dTurn: number; well: number }

/** RANGE of theta(t) = c1 t + c2 t^2 over [0,1] (relative to th0). */
function thetaRange(c1: number, c2: number): number {
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
function closeAt(p0: V, th0: number, p1: V, tau: number, c1Init: number, LInit: number): { c1: number; L: number; ok: boolean } {
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
const RANGE_B = Math.PI
const WELL_S = 25
function legInnerE(sol: { c1: number; L: number }, tau: number, arriveErr: number): number {
  const c2 = tau - sol.c1
  return P.tension * sol.L
    + (P.bend * (sol.c1 * sol.c1 + 2 * sol.c1 * c2 + (4 / 3) * c2 * c2)) / sol.L
    + WELL_S * (1 - Math.cos(arriveErr))
}
/** EXACT arc closure (c2 = 0 member of the family), closed form: the
    unique circle through p0 tangent to th0 that passes p1. Always exists,
    always closes exactly, smooth in its inputs — the deterministic seed
    and the guaranteed fallback (an unconverged Newton used to leave the
    drawn endpoint hanging off the rim, flickering frame to frame). */
function arcClose(p0: V, th0: number, p1: V): { tau: number; L: number } {
  const chord = hyp(p1.x - p0.x, p1.y - p0.y)
  const delta = wrapA(Math.atan2(p1.y - p0.y, p1.x - p0.x) - th0)
  const s = Math.abs(delta) < 1e-6 ? 1 : delta / Math.sin(delta)
  return { tau: 2 * delta, L: Math.max(chord * s, 0.01) }
}
function solveLeg(leg: Leg, p0: V, th0: number, p1: V, th1: number, freeEnd: boolean): Sol {
  const k = leg.cacheK
  if (k !== null && k[0] === p0.x && k[1] === p0.y && k[2] === th0 && k[3] === p1.x && k[4] === p1.y && k[5] === th1) return leg.cacheS!
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
  leg.cacheK = [p0.x, p0.y, th0, p1.x, p1.y, th1]
  leg.cacheS = sol
  return sol
}

/** Solve + trace every leg of a wire; boundary tangents by leg kind. */
function legGeom(w: Wire, leg: Leg): { sol: Sol; p0: V; th0: number; th1: number } {
  const r0 = rim(leg.a)
  let p1: V, th1: number
  if (leg.b === 'hub') {
    p1 = w.hub!
    // trunk legs 0,1 arrive along the axis (opposite senses); side legs
    // arrive tangent to it — the tributary rule as boundary conditions
    // every hub leg's arrival direction is its own relaxing DOF: fixed
    // role assignments could not swap leg order and compensated with
    // loose spirals (USER report); a finite angular-spacing energy keeps
    // them spread (Plateau) yet lets them pass each other under stress
    th1 = w.hubT[w.legs.indexOf(leg)]!
  } else if (leg.b === 'tip') {
    // a dangling end is a FREE END of the elastic rod: zero moment,
    // no prescribed tangent (the stiff tip/tipT coupling made the dot
    // crawl — coordinate descent zigzagged against the well)
    p1 = w.tip!
    th1 = 0
  } else {
    const r1 = rim(leg.b)
    p1 = r1.p
    th1 = r1.n + Math.PI // arrive INTO the far port against its normal
  }
  return { sol: solveLeg(leg, r0.p, r0.n, p1, th1, leg.b === 'tip'), p0: r0.p, th0: r0.n, th1 }
}

// ---- ONE energy over body/hub/tip DOF only ---------------------------------
function clearU(d: number, R: number): number {
  if (d >= R) return 0
  const h = R / 2
  if (d >= h) { const t = (R - d) / h; return (P.clearSlope * h * t * t) / 2 }
  return (P.clearSlope * h) / 2 + P.clearSlope * (h - d)
}
const sampScratch: V[][] = []
let EVALS = 0
function energy(): number {
  EVALS++
  let E = 0
  let si = 0
  const wireSamples: { from: number; to: number }[] = []
  for (const w of wires) {
    const from = si
    for (const leg of w.legs) {
      const { sol, p0, th0 } = legGeom(w, leg)
      E += P.tension * sol.L
      // ∫k^2 ds closed form: k(t) = (c1 + 2 c2 t)/L — plus the arrival
      // well (the strained exit IS energy: force builds toward buckling)
      E += (P.bend * (sol.c1 * sol.c1 + 2 * sol.c1 * sol.c2 + (4 / 3) * sol.c2 * sol.c2)) / sol.L
      E += sol.well
      if (sampScratch[si] === undefined) sampScratch[si] = []
      trace(p0, th0, sol.c1, sol.c2, sol.L, sampScratch[si]!)
      // node clearance line integral (own end discs exempt near their rim
      // by geometry: the curve starts ON the rim heading outward)
      const s = sampScratch[si]!
      const ds = sol.L / QN
      const ownA = leg.a.disc, ownB = leg.b !== 'hub' && leg.b !== 'tip' ? leg.b.disc : -1
      for (let k = 1; k < s.length; k++) {
        for (let di = 0; di < discs.length; di++) {
          const D = discs[di]!
          const R = D.r + P.clearMargin
          const d = hyp(s[k]!.x - D.pos.x, s[k]!.y - D.pos.y)
          if (d >= R) continue
          let m = 1
          if (di === ownA || di === ownB) {
            const arc = di === ownA ? k * ds : (s.length - 1 - k) * ds
            m = Math.max(0, Math.min(1, (arc - R) / R))
          }
          E += m * clearU(d, R) * ds
        }
      }
      si++
    }
    wireSamples.push({ from, to: si })
  }
  // wire-wire separation: crossings spend no arc in the band, co-running does
  for (let a = 0; a < wireSamples.length; a++) for (let b = a + 1; b < wireSamples.length; b++) {
    for (let i = wireSamples[a]!.from; i < wireSamples[a]!.to; i++) {
      for (let j = wireSamples[b]!.from; j < wireSamples[b]!.to; j++) {
        const sa = sampScratch[i]!, sb = sampScratch[j]!
        for (let k = 0; k < sa.length; k += 3) for (let l = 0; l < sb.length; l += 3) {
          const d = hyp(sa[k]!.x - sb[l]!.x, sa[k]!.y - sb[l]!.y)
          if (d < P.sepR) E += P.sepSlope * (P.sepR - d) * (P.sepR - d) / P.sepR
        }
      }
    }
  }
  for (const w of wires) {
    // hub legs spread apart (min at 120 for three); FINITE height, so leg
    // order can swap by passing through — no frozen role assignment
    for (let i = 0; i < w.hubT.length; i++) for (let j = i + 1; j < w.hubT.length; j++) {
      E += 10 * (1 + Math.cos(w.hubT[i]! - w.hubT[j]!)) / 2
    }
    // the dangle dot must never sink into the edge it hangs from (USER):
    // C1 standoff vs its rim anchor, slope 2·tension (dominates the pull
    // on an endpoint, which is exactly one tension)
    if (w.tip !== null) {
      const r0 = rim(w.legs[0]!.a)
      const d = hyp(w.tip.x - r0.p.x, w.tip.y - r0.p.y)
      const R = 8
      if (d < R) {
        const h = R / 2
        const slope = 2 * P.tension
        E += d >= h ? (slope * h * ((R - d) / h) ** 2) / 2 : (slope * h) / 2 + slope * (h - d)
      }
    }
  }
  for (let i = 0; i < discs.length; i++) for (let j = i + 1; j < discs.length; j++) {
    const A = discs[i]!, B = discs[j]!
    const need = A.r + B.r + 12
    const d = hyp(A.pos.x - B.pos.x, A.pos.y - B.pos.y)
    if (d < need) E += 3 * (need - d) * (need - d)
    E += 0.0004 * d * d
  }
  return E
}

// ---- strict per-DOF descent (bodies, hubs, tips only) -----------------------
type Dof = { get: () => number; set: (v: number) => void; mob: number; h: number; cap: number }
const MU = 0.1, HX = 0.02
function dofs(dragging: string | null): Dof[] {
  const out: Dof[] = []
  const pv = (p: V): void => {
    out.push({ get: () => p.x, set: (v) => { p.x = v }, mob: MU, h: HX, cap: 0.28 })
    out.push({ get: () => p.y, set: (v) => { p.y = v }, mob: MU, h: HX, cap: 0.28 })
  }
  for (const w of wires) {
    if (w.hub !== null) {
      pv(w.hub)
      for (let i = 0; i < w.hubT.length; i++) {
        out.push({ get: () => w.hubT[i]!, set: (v) => { w.hubT[i] = v }, mob: MU / 64, h: HX / 8, cap: 0.06 })
      }
    }
    if (w.tip !== null) {
      // the dot is the smallest body in the system — mobility to match
      out.push({ get: () => w.tip!.x, set: (v) => { w.tip!.x = v }, mob: 3 * MU, h: HX, cap: 0.55 })
      out.push({ get: () => w.tip!.y, set: (v) => { w.tip!.y = v }, mob: 3 * MU, h: HX, cap: 0.55 })
    }
  }
  for (const D of discs) {
    if (D.id === dragging) continue
    pv(D.pos)
    // rotation relaxes 4x faster than rim-speed parity: rotating is
    // collision-free, and the USER spec'd snappier edge-relaxing rotation
    out.push({ get: () => D.theta, set: (v) => { D.theta = v }, mob: (4 * MU) / (D.r * D.r), h: HX / D.r, cap: 0.28 })
  }
  return out
}
// ANYTIME descent: each frame spends a fixed wall-time budget walking the
// DOF ring (resuming where it left off), so the UI stays at display rate
// no matter what the solver costs — progress per second is the knob, not
// frame rate.
let cursor = 0
function tickBudget(dragging: string | null, budgetMs: number): void {
  const ds = dofs(dragging)
  if (ds.length === 0) return
  let E = energy()
  const t0 = performance.now()
  let visited = 0
  while (performance.now() - t0 < budgetMs && visited < ds.length * 4) {
    const d = ds[cursor % ds.length]!
    cursor++
    visited++
    const v0 = d.get()
    d.set(v0 + d.h); const ep = energy()
    d.set(v0 - d.h); const em = energy()
    d.set(v0)
    const g = (ep - em) / (2 * d.h)
    if (g === 0) continue
    let mv = Math.max(-d.cap, Math.min(d.cap, -g * d.mob))
    let acceptedMv = 0
    for (let k = 0; k < 3; k++) {
      d.set(v0 + mv)
      const E1 = energy()
      if (E1 < E) { E = E1; acceptedMv = mv; break }
      d.set(v0)
      mv /= 4
    }
    if (acceptedMv === 0) {
      // smooth step rejected: LONG-SHOT ladder from the trust-region cap
      // downward, strictly gated — crosses local hills narrower than the
      // cap (a wrenched node sat in a 60-degree-off torque minimum with
      // the way back over a branch-switch ridge; USER: nodes don't rotate
      // near as much as they could)
      const dir = g > 0 ? -1 : 1
      for (const frac of [1, 1 / 3, 1 / 9]) {
        d.set(v0 + dir * d.cap * frac)
        const E1 = energy()
        if (E1 < E) { E = E1; acceptedMv = dir * d.cap * frac; break }
        d.set(v0)
      }
    }
    // EXPANDING search: a DOF far from rest should cover distance in one
    // visit, not one mobility-quantum per ring pass (the teleported-tip
    // crawl); keep tripling while E strictly drops, capped by the trust
    // region
    while (acceptedMv !== 0 && Math.abs(acceptedMv) < d.cap) {
      const next = Math.max(-d.cap, Math.min(d.cap, acceptedMv * 3))
      d.set(v0 + next)
      const E2 = energy()
      if (E2 < E) { E = E2; acceptedMv = next }
      else { d.set(v0 + acceptedMv); break }
      if (Math.abs(acceptedMv) >= d.cap) break
    }
  }
}

// ---- page --------------------------------------------------------------------
document.body.style.cssText = 'margin:0;background:#f6f1e7;font:13px system-ui'
const head = document.createElement('div')
head.style.cssText = 'padding:8px 12px;background:#fffdf8;border-bottom:1px solid #ddd'
head.innerHTML = '<b>Round 10 — wires are massless elastica</b> — zero wire DOF: each wire IS the unique minimum-bend Euler-spiral interpolant of its ports; kinks AND loops unrepresentable; bodies/hubs/tips carry all the physics; drag any disc'
document.body.append(head)
const canvas = document.createElement('canvas')
canvas.style.cssText = 'position:fixed;inset:42px 0 0 0'
document.body.append(canvas)
const ctx = canvas.getContext('2d')!

let dragging: string | null = null
let dragOff: V = { x: 0, y: 0 }
const view = { s: 2.2 }
const toWorld = (mx: number, my: number): V => ({ x: (mx - canvas.width / 2) / view.s, y: (my - canvas.height / 2 - 42) / view.s })
canvas.addEventListener('pointerdown', (e) => {
  const w = toWorld(e.clientX, e.clientY)
  for (const D of discs) if (hyp(w.x - D.pos.x, w.y - D.pos.y) < D.r + 3) {
    dragging = D.id
    dragOff = { x: D.pos.x - w.x, y: D.pos.y - w.y }
    canvas.setPointerCapture(e.pointerId)
  }
})
canvas.addEventListener('pointermove', (e) => {
  if (dragging === null) return
  const D = discs.find((d) => d.id === dragging)!
  const w = toWorld(e.clientX, e.clientY)
  D.pos.x = w.x + dragOff.x
  D.pos.y = w.y + dragOff.y
})
canvas.addEventListener('pointerup', () => { dragging = null })

const paintPts: V[] = []
function paint(): void {
  const W = window.innerWidth, H = window.innerHeight - 42
  if (canvas.width !== W) canvas.width = W
  if (canvas.height !== H) canvas.height = H
  ctx.setTransform(1, 0, 0, 1, 0, 0)
  ctx.clearRect(0, 0, W, H)
  ctx.setTransform(view.s, 0, 0, view.s, W / 2, H / 2)
  ctx.lineWidth = 1.45
  ctx.strokeStyle = '#2b3038'
  ctx.lineCap = 'round'
  ctx.lineJoin = 'round'
  for (const w of wires) {
    for (const leg of w.legs) {
      const { sol, p0, th0 } = legGeom(w, leg)
      trace(p0, th0, sol.c1, sol.c2, sol.L, paintPts, 30)
      ctx.beginPath()
      ctx.moveTo(paintPts[0]!.x, paintPts[0]!.y)
      for (const q of paintPts) ctx.lineTo(q.x, q.y)
      ctx.stroke()
    }
    if (w.tip !== null) {
      ctx.beginPath()
      ctx.arc(w.tip.x, w.tip.y, 2.4, 0, Math.PI * 2)
      ctx.fillStyle = '#2b3038'
      ctx.fill()
    }
  }
  for (const D of discs) {
    ctx.beginPath()
    ctx.arc(D.pos.x, D.pos.y, D.r, 0, Math.PI * 2)
    ctx.fillStyle = '#fffdf8'
    ctx.fill()
    ctx.stroke()
    ctx.fillStyle = '#2b3038'
    ctx.font = '9px Georgia'
    ctx.textAlign = 'center'
    ctx.textBaseline = 'middle'
    ctx.fillText(D.id, D.pos.x, D.pos.y)
    for (const pa of D.ports) {
      const a = D.theta + pa
      ctx.beginPath()
      ctx.arc(D.pos.x + Math.cos(a) * D.r, D.pos.y + Math.sin(a) * D.r, 1.6, 0, Math.PI * 2)
      ctx.fill()
    }
  }
}
function maxResidual(): number {
  let worst = 0
  for (const w of wires) for (const leg of w.legs) {
    const { sol, p0, th0 } = legGeom(w, leg)
    trace(p0, th0, sol.c1, sol.c2, sol.L, tr)
    const e = tr[tr.length - 1]!
    let target: V
    if (leg.b === 'hub') target = w.hub!
    else if (leg.b === 'tip') target = w.tip!
    else target = rim(leg.b).p
    worst = Math.max(worst, hyp(e.x - target.x, e.y - target.y))
  }
  return worst
}
;(window as unknown as { __r10: unknown }).__r10 = { discs, wires, energy, evals: () => EVALS, maxResidual }
const frame = (): void => {
  tickBudget(dragging, 8)
  paint()
  requestAnimationFrame(frame)
}
requestAnimationFrame(frame)
