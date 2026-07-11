/**
 * ROUND 9 — THE BEZIER CONTROL POINTS ARE THE PHYSICS (corpus synthesis).
 *
 * Wire state = at most a few free control points per leg; the drawn Hobby
 * spline through them IS the simulated object. Kinks and node-wraps are
 * unrepresentable (a 2-control-point curve cannot kink or wind); nothing
 * discrete exists (no topology moves, no resampling, no routing) so nothing
 * can ever snap. One scalar energy over all DOF (control points, junctions,
 * ∃ tips, disc positions AND rotations), damped numerical gradient descent:
 *   E = tension·length + bend·∫κ²ds + Σ discs ∫U_clear ds (saturating,
 *       reciprocal — wires push discs, discs push and TORQUE wires' nodes)
 *     + Σ wire pairs ∫U_sep ds (small radius: transverse crossings spend no
 *       arc inside the band = cheap; co-running overlap = long = pushed apart)
 * Endpoints are rim-locked with perpendicular exit stubs BY CONSTRUCTION.
 */

type V = { x: number; y: number }
const hyp = Math.hypot

// ---- model ----------------------------------------------------------------
type Disc = { id: string; pos: V; theta: number; r: number; ports: number[] }
type End = { disc: number; port: number }
type Leg = { end: End | null; ctrl: V[] } // end=null → leg runs to the wire's hub (junction/tip)
type Wire = { legs: Leg[]; hub: V | null; tip: boolean } // hub: junction (3-way) or ∃ tip (dangle)

const P = { tension: 1.0, bend: 14, clearSlope: 3.2, clearMargin: 5, sepSlope: 1.4, sepR: 5, stub: 7 }

const discs: Disc[] = [
  { id: 'plus', pos: { x: -70, y: -20 }, theta: 0.3, r: 16, ports: [0, 2.1, 4.2] },
  { id: 'times', pos: { x: 60, y: -55 }, theta: 1.2, r: 16, ports: [0, 2.1, 4.2] },
  { id: 'succ', pos: { x: 85, y: 45 }, theta: -0.8, r: 14, ports: [0, Math.PI] },
  { id: 'zero', pos: { x: -15, y: 70 }, theta: 0.5, r: 12, ports: [0] },
  { id: 'nat', pos: { x: -95, y: 70 }, theta: -0.4, r: 13, ports: [0, Math.PI] },
  { id: 'lt', pos: { x: 5, y: -95 }, theta: 1.9, r: 13, ports: [0, Math.PI] },
]

const mk2 = (a: End, b: End): Wire => ({ legs: [{ end: a, ctrl: [{ x: 0, y: 0 }, { x: 0, y: 0 }] }, { end: b, ctrl: [] }], hub: null, tip: false })
const wires: Wire[] = [
  // 3-way: plus, times, succ share a line (junction hub, one ctrl per leg)
  {
    legs: [
      { end: { disc: 0, port: 0 }, ctrl: [{ x: 0, y: 0 }] },
      { end: { disc: 1, port: 0 }, ctrl: [{ x: 0, y: 0 }] },
      { end: { disc: 2, port: 0 }, ctrl: [{ x: 0, y: 0 }] },
    ],
    hub: { x: 20, y: -10 }, tip: false,
  },
  mk2({ disc: 0, port: 1 }, { disc: 3, port: 0 }),   // plus—zero
  mk2({ disc: 1, port: 1 }, { disc: 4, port: 0 }),   // times—nat (long, crosses)
  mk2({ disc: 0, port: 2 }, { disc: 5, port: 0 }),   // plus—lt
  mk2({ disc: 5, port: 1 }, { disc: 2, port: 1 }),   // lt—succ (crosses times—nat)
  // dangle off nat: leg to a free ∃ tip
  { legs: [{ end: { disc: 4, port: 1 }, ctrl: [{ x: 0, y: 0 }] }], hub: { x: -130, y: 90 }, tip: true },
]

// seed control points along the straight line between their leg's endpoints
function rim(end: End): { p: V; n: number } {
  const d = discs[end.disc]!
  const a = d.theta + d.ports[end.port]!
  return { p: { x: d.pos.x + Math.cos(a) * d.r, y: d.pos.y + Math.sin(a) * d.r }, n: a }
}
for (const w of wires) {
  for (const leg of w.legs) {
    const a = leg.end !== null ? rim(leg.end).p : w.hub!
    const bEnd = w.legs.find((l) => l !== leg && l.end !== null)?.end
    const b = w.hub ?? (bEnd !== undefined ? rim(bEnd).p : a)
    leg.ctrl.forEach((c, i) => {
      const t = (i + 1) / (leg.ctrl.length + 1)
      c.x = a.x + (b.x - a.x) * t + 6
      c.y = a.y + (b.y - a.y) * t - 4
    })
  }
}

// ---- curve construction (what is drawn IS what is simulated) --------------
const wrapA = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))
function hobbyRho(t: number, f: number): number {
  const a = Math.sqrt(2), b = 1 / 16, c = (3 - Math.sqrt(5)) / 2
  return (2 + a * (Math.sin(t) - b * Math.sin(f)) * (Math.sin(f) - b * Math.sin(t)) * (Math.cos(t) - Math.cos(f))) /
    (1 + (1 - c) * Math.cos(t) + c * Math.cos(f))
}
type Cubic = { a: V; c1: V; c2: V; b: V }
function hobbySeg(pa: V, ta: number, pb: V, tb: number): Cubic {
  const chord = Math.atan2(pb.y - pa.y, pb.x - pa.x)
  const d = hyp(pb.x - pa.x, pb.y - pa.y)
  const th = wrapA(ta - chord), ph = wrapA(chord - (tb + Math.PI))
  const ra = Math.abs(hobbyRho(th, ph)) * d / 3, rb = Math.abs(hobbyRho(ph, th)) * d / 3
  return { a: pa, c1: { x: pa.x + Math.cos(ta) * ra, y: pa.y + Math.sin(ta) * ra }, c2: { x: pb.x + Math.cos(tb) * rb, y: pb.y + Math.sin(tb) * rb }, b: pb }
}

/** A leg's spline: rim point (tangent = port normal, the perpendicular exit
    boundary condition) through its control points to the hub or the paired
    leg's rim. Returns hobby cubics; sampled for both painting and energy. */
function legAnchors(w: Wire, leg: Leg): { pts: V[]; t0: number; t1: number } {
  const pts: V[] = []
  let t0: number, t1: number
  if (leg.end !== null) {
    const r0 = rim(leg.end)
    pts.push(r0.p)
    t0 = r0.n
  } else { pts.push(w.hub!); t0 = 0 }
  pts.push(...leg.ctrl)
  if (w.hub !== null) { pts.push(w.hub); t1 = 0 } else {
    const other = w.legs.find((l) => l !== leg)!
    const r1 = rim(other.end!)
    pts.push(...[...other.ctrl].reverse(), r1.p)
    t1 = r1.n
  }
  return { pts, t0, t1 }
}
function catmull(pts: V[], i: number): number {
  const a = pts[Math.max(0, i - 1)]!, b = pts[Math.min(pts.length - 1, i + 1)]!
  return Math.atan2(b.y - a.y, b.x - a.x)
}
function wireCubics(w: Wire): Cubic[][] {
  const paths: Cubic[][] = []
  const emit = (w2: Wire, leg: Leg): Cubic[] => {
    const { pts, t0, t1 } = legAnchors(w2, leg)
    // FORWARD travel direction at each anchor; hobbySeg takes OUTWARD
    // tangents at both ends (start: forward; end: forward + pi), except a
    // far rim, whose outward tangent IS its port normal
    const fwd = pts.map((_, i) => {
      if (i === 0 && leg.end !== null) return t0
      return catmull(pts, i)
    })
    const out: Cubic[] = []
    for (let i = 0; i + 1 < pts.length; i++) {
      const last = i + 1 === pts.length - 1
      const tb = last && w2.hub === null ? t1 : fwd[i + 1]! + Math.PI
      out.push(hobbySeg(pts[i]!, fwd[i]!, pts[i + 1]!, tb))
    }
    return out
  }
  if (w.hub !== null) for (const leg of w.legs) paths.push(emit(w, leg))
  else paths.push(emit(w, w.legs[0]!))
  return paths
}
const SUB = 7
function sampleWire(w: Wire): V[] {
  const out: V[] = []
  for (const path of wireCubics(w)) for (const c of path) {
    for (let k = 0; k < SUB; k++) {
      const t = k / SUB, u = 1 - t
      out.push({
        x: u * u * u * c.a.x + 3 * u * u * t * c.c1.x + 3 * u * t * t * c.c2.x + t * t * t * c.b.x,
        y: u * u * u * c.a.y + 3 * u * u * t * c.c1.y + 3 * u * t * t * c.c2.y + t * t * t * c.b.y,
      })
    }
  }
  return out
}

// ---- the ONE energy --------------------------------------------------------
function clearU(d: number, R: number): number {
  if (d >= R) return 0
  const h = R / 2
  if (d >= h) { const t = (R - d) / h; return (P.clearSlope * h * t * t) / 2 }
  return (P.clearSlope * h) / 2 + P.clearSlope * (h - d)
}
function energy(): number {
  let E = 0
  const samples = wires.map(sampleWire)
  for (let wi = 0; wi < wires.length; wi++) {
    const s = samples[wi]!
    const own = new Set(wires[wi]!.legs.map((l) => l.end?.disc))
    // rim points of this wire, for the smooth own-disc exemption ramp
    const rims = wires[wi]!.legs.filter((l) => l.end !== null).map((l) => rim(l.end!).p)
    for (let i = 0; i + 1 < s.length; i++) {
      const dx = s[i + 1]!.x - s[i]!.x, dy = s[i + 1]!.y - s[i]!.y
      const ds = hyp(dx, dy)
      E += P.tension * ds
      if (i + 2 < s.length) {
        const ex = s[i + 2]!.x - s[i + 1]!.x, ey = s[i + 2]!.y - s[i + 1]!.y
        const el = hyp(ex, ey)
        if (ds > 1e-9 && el > 1e-9) {
          const turn = wrapA(Math.atan2(ey, ex) - Math.atan2(dy, dx))
          E += (P.bend * turn * turn) / Math.max(0.5, (ds + el) / 2)
        }
      }
      // node clearance along the curve (skip near own rims: the attachment
      // region is INSIDE the disc by construction; ramp back in smoothly)
      for (let di = 0; di < discs.length; di++) {
        const D = discs[di]!
        const R = D.r + P.clearMargin
        const d = hyp(s[i]!.x - D.pos.x, s[i]!.y - D.pos.y)
        if (d >= R) continue
        let m = 1
        if (own.has(di)) {
          let near = Infinity
          for (const rp of rims) near = Math.min(near, hyp(s[i]!.x - rp.x, s[i]!.y - rp.y))
          m = Math.max(0, Math.min(1, (near - P.stub) / P.stub))
        }
        E += m * clearU(d, R) * ds
      }
    }
    // wire↔wire separation (coarse pairs; transverse crossings are cheap)
    for (let wj = wi + 1; wj < wires.length; wj++) {
      const t = samples[wj]!
      for (let i = 0; i < s.length; i += 2) for (let j = 0; j < t.length; j += 2) {
        const d = hyp(s[i]!.x - t[j]!.x, s[i]!.y - t[j]!.y)
        if (d < P.sepR) E += P.sepSlope * (P.sepR - d) * (P.sepR - d) / P.sepR
      }
    }
  }
  // discs: pairwise spacing (content law: circles never intersect)
  for (let i = 0; i < discs.length; i++) for (let j = i + 1; j < discs.length; j++) {
    const A = discs[i]!, B = discs[j]!
    const need = A.r + B.r + 12
    const d = hyp(A.pos.x - B.pos.x, A.pos.y - B.pos.y)
    if (d < need) E += 3 * (need - d) * (need - d)
    E += 0.0004 * d * d // weak cohesion
  }
  return E
}

// ---- descent over ALL DOF: one mobility, dimensionally consistent ---------
// Positions live in length units; theta is converted to its rim-arc metric
// (mobility mu/r^2, probed at the same rim displacement as positions), so a
// single mobility governs everything — no per-kind magic steps. Every tick
// is E-GATED: if the proposed step raises the energy it is halved until it
// descends, and a tick that cannot descend leaves the state exactly at
// rest. Monotone E is the settling guarantee (the plan-21 discipline);
// without it the fixed step rang nat's rotation +-0.24 rad forever.
type Dof = { get: () => number; set: (v: number) => void; mob: number; h: number; cap: number }
const MU = 0.06
const HX = 0.02
function dofs(dragging: string | null): Dof[] {
  const out: Dof[] = []
  const pv = (p: V): void => {
    out.push({ get: () => p.x, set: (v) => { p.x = v }, mob: MU, h: HX, cap: 0.9 })
    out.push({ get: () => p.y, set: (v) => { p.y = v }, mob: MU, h: HX, cap: 0.9 })
  }
  for (const w of wires) {
    for (const leg of w.legs) for (const c of leg.ctrl) pv(c)
    if (w.hub !== null) pv(w.hub)
  }
  for (const D of discs) {
    if (D.id === dragging) continue
    pv(D.pos)
    out.push({ get: () => D.theta, set: (v) => { D.theta = v }, mob: MU / (D.r * D.r), h: HX / D.r, cap: 0.9 / D.r })
  }
  return out
}
function tick(dragging: string | null): number {
  // COORDINATE descent, strictly E-gated per DOF: a monolithic all-DOF
  // step lets one stiff direction (whose smallest scaled move still
  // raises E) veto the whole tick — the state froze with wires left long
  // and bowed while single-DOF descent was plainly available (USER
  // report). Per-DOF line search rests only when NO degree of freedom
  // can strictly descend; E remains strictly monotone, so no cycles.
  const ds = dofs(dragging)
  let E = energy()
  let maxMove = 0
  for (const d of ds) {
    const v0 = d.get()
    d.set(v0 + d.h); const ep = energy()
    d.set(v0 - d.h); const em = energy()
    d.set(v0)
    const g = (ep - em) / (2 * d.h)
    if (g === 0) continue
    let mv = Math.max(-d.cap, Math.min(d.cap, -g * d.mob))
    let accepted = false
    for (let k = 0; k < 3 && !accepted; k++) {
      d.set(v0 + mv)
      const E1 = energy()
      if (E1 < E) { E = E1; accepted = true; maxMove = Math.max(maxMove, Math.abs(mv)) }
      else { d.set(v0); mv /= 4 }
    }
  }
  return maxMove
}

// ---- page -------------------------------------------------------------------
document.body.style.cssText = 'margin:0;background:#f6f1e7;font:13px system-ui'
const head = document.createElement('div')
head.style.cssText = 'padding:8px 12px;background:#fffdf8;border-bottom:1px solid #ddd'
head.innerHTML = '<b>Round 9 — the Bézier control points ARE the physics</b> — wire = spline through ≤2 free points: kinks and node-wraps unrepresentable, nothing discrete → nothing can snap; curves avoid nodes, push and torque them, decline to co-run; drag any disc'
document.body.append(head)
const canvas = document.createElement('canvas')
canvas.style.cssText = 'position:fixed;inset:42px 0 0 0'
document.body.append(canvas)
const ctx = canvas.getContext('2d')!

let dragging: string | null = null
let dragOff: V = { x: 0, y: 0 }
const view = { s: 2.2, cx: 0, cy: 0 }
const toWorld = (mx: number, my: number): V => ({ x: (mx - canvas.width / 2) / view.s + view.cx, y: (my - canvas.height / 2 - 42) / view.s + view.cy })
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

function paint(): void {
  const W = window.innerWidth, H = window.innerHeight - 42
  if (canvas.width !== W) canvas.width = W
  if (canvas.height !== H) canvas.height = H
  ctx.setTransform(1, 0, 0, 1, 0, 0)
  ctx.clearRect(0, 0, W, H)
  ctx.setTransform(view.s, 0, 0, view.s, W / 2 - view.cx * view.s, H / 2 - view.cy * view.s)
  ctx.lineWidth = 1.6 / view.s * 2
  ctx.strokeStyle = '#2b3038'
  ctx.lineCap = 'round'
  for (const w of wires) {
    for (const path of wireCubics(w)) {
      ctx.beginPath()
      ctx.moveTo(path[0]!.a.x, path[0]!.a.y)
      for (const c of path) ctx.bezierCurveTo(c.c1.x, c.c1.y, c.c2.x, c.c2.y, c.b.x, c.b.y)
      ctx.stroke()
    }
    if (w.tip && w.hub !== null) {
      ctx.beginPath()
      ctx.arc(w.hub.x, w.hub.y, 2.4, 0, Math.PI * 2)
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
;(window as unknown as { __r9: unknown }).__r9 = { discs, wires, energy }
const frame = (): void => {
  for (let i = 0; i < 3; i++) tick(dragging)
  paint()
  requestAnimationFrame(frame)
}
requestAnimationFrame(frame)
