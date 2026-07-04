import type { Vec2 } from './vec'

/**
 * PLAN 21 — wires as first-class physical objects (the energy core).
 *
 * A wire is a TREE of chain points: terminals (port-bound, homed ∃/∀ bodies,
 * or boundary-slot pins) joined through sampled interior points. It carries
 * ONE energy; every force here is the negative gradient of a named term;
 * damped gradient descent with a trust region is the only integrator; the
 * discrete topology moves (split/merge at junction points) are accepted only
 * when they strictly lower the energy. No other state writes exist — that is
 * the whole discipline (USER: "this should still be energy based; I don't
 * want to end up in the previous mess").
 *
 *   E_wire = WIREP.tension · Σ|segment|                      (wants to be short)
 *          + WIREP.bend · Σ turn²                            (wants to be straight)
 *          + Σ barrier(disc, point)                    (wires ↔ nodes, symmetric)
 *
 * The barrier potential is finite-depth (saturating force — the engine's
 * SOFT discipline): U(d) = BARRIER_DEPTH · (1 − d/r)² inside the disc's
 * clearance radius r, zero outside. Its gradient pushes the wire point out
 * AND the disc away with equal magnitude — callers must apply the returned
 * disc reactions, which is what makes wires push nodes.
 */

/** LIVE-TUNABLE wire parameters (the feel levers — ui-lab/tune.html).
    Defaults are the values every law in the battery was pinned against.
    Constraints that stay true at any setting: barrierSlope must exceed the
    content soft cap (≈11.7) or attracted discs plow through wires
    (measured); travelCap bounds drawn per-tick motion (continuity law). */
export const WIREP = {
  /** wire shortness: unit pull along the chain */
  tension: 1.0,
  /** straightness stiffness (∫κ²ds weight); junction angles deviate from
      120° in proportion (soap limit at 0) */
  bend: 0.6,
  /** disc↔wire push, saturated slope (see constraint above) */
  barrierSlope: 18,
  /** how far beyond a disc's radius wires keep clear */
  clearanceMargin: 1.5,
  /** trust region: max drawn wire motion per tick */
  travelCap: 0.5,
}
/** There is NO spacing energy term. Three formulations were built and
    measured before concluding the term itself is wrong: a symmetric rest
    length makes the chain an inextensible rope of its birth length
    (coiling swimmers); a one-sided compression floor locks surplus length
    into standing wrinkles (a stretched dangle could never re-contract);
    pure adjacent-uniformity lets whole paths collapse together. The
    parameterization is a GAUGE and is handled outside the energy by the
    canonical resample (E-neutral now that every term is a proper continuum
    discretization), while the invariant bend term turn²/arc-share already
    diverges when a CURVED point bunches — the one case where bunching
    hurts the drawing. */
/** Sampling pitch (wu) between chain points; resample beyond 2× drift. */
export const PITCH = 2
/** Point budget per rebuilt path: transient chains can be HUNDREDS of wu
    long (spiral-seeded bodies), and pitch-sampling them explodes per-tick
    work quadratically before contraction shrinks anything (measured: a
    bundled-theory paint test at 226 s and a call-stack overflow). Coarse
    segments stay energetically honest — the barrier is a per-segment line
    integral and the bend is arc-share-invariant. */
export const MAX_PATH_PTS = 64

export type ChainBind = { idx: number; body: string; key: string; normal?: number }
export type ChainHomed = { idx: number; bodyId: string }

export type WireChain = {
  pts: Vec2[]
  /** tree adjacency over pts */
  adj: number[][]
  /** port-pinned terminals (constraint: pts[idx] = the port anchor) */
  binds: ChainBind[]
  /** wire-points that are also region-member bodies (∃ ends, ∀-dangle tips):
      the BODY owns the DOF; the chain mirrors it and contributes its wire
      gradient as a force on the body. */
  homed: ChainHomed[]
  /** boundary terminals pinned to canonical frame slots (constraint). */
  slots: { idx: number; slot: number }[]
  pitch: number
}

export type ChainDisc = { id: string; pos: Vec2; r: number }

/** Mutable accumulator vector (Vec2 is readonly by convention). */
type MVec = { x: number; y: number }

const sub = (a: Vec2, b: Vec2): Vec2 => ({ x: a.x - b.x, y: a.y - b.y })
const len = (a: Vec2): number => Math.hypot(a.x, a.y)

/** Build a chain: terminals plus a subdivided star/path through them.
    2 terminals → a straight sampled path; ≥3 → a star through one interior
    junction point at the centroid (topology descent refines it during
    settling); 1 terminal is a caller error (a 1-endpoint wire's second
    terminal is its homed ∃ end — the caller supplies BOTH). */
export function mkChain(terminals: Vec2[], pitch: number): { pts: Vec2[]; adj: number[][] } {
  if (terminals.length < 2) throw new Error(`mkChain needs >=2 terminals, got ${terminals.length}`)
  const pts: Vec2[] = terminals.map((t) => ({ ...t }))
  const adj: number[][] = terminals.map(() => [])
  const link = (a: number, b: number): void => {
    adj[a]!.push(b)
    adj[b]!.push(a)
  }
  const subdividedLink = (a: number, b: number): void => {
    const d = len(sub(pts[b]!, pts[a]!))
    const k = Math.min(MAX_PATH_PTS, Math.max(1, Math.round(d / pitch)))
    let prev = a
    for (let i = 1; i < k; i++) {
      const t = i / k
      const idx = pts.length
      pts.push({ x: pts[a]!.x + (pts[b]!.x - pts[a]!.x) * t, y: pts[a]!.y + (pts[b]!.y - pts[a]!.y) * t })
      adj.push([])
      link(prev, idx)
      prev = idx
    }
    link(prev, b)
  }
  if (terminals.length === 2) {
    subdividedLink(0, 1)
    return { pts, adj }
  }
  const cx = terminals.reduce((s, t) => s + t.x, 0) / terminals.length
  const cy = terminals.reduce((s, t) => s + t.y, 0) / terminals.length
  const hub = pts.length
  pts.push({ x: cx, y: cy })
  adj.push([])
  for (let t = 0; t < terminals.length; t++) subdividedLink(t, hub)
  return { pts, adj }
}

/** Barrier potential: gradient ramps 0 → WIREP.barrierSlope over the outer half
    of the clearance zone, constant WIREP.barrierSlope inside. */
export function barrierU(d: number, r: number): number {
  if (d >= r) return 0
  const half = r / 2
  if (d >= half) {
    const t = (r - d) / half // 0 at rim, 1 at half depth
    return (WIREP.barrierSlope * half * t * t) / 2
  }
  return (WIREP.barrierSlope * half) / 2 + WIREP.barrierSlope * (half - d)
}

export function barrierG(d: number, r: number): number {
  if (d >= r) return 0
  const half = r / 2
  if (d >= half) return (WIREP.barrierSlope * (r - d)) / half
  return WIREP.barrierSlope
}

/** The barrier clearance radius of a disc for wire points. */
export const clearance = (r: number): number => r + WIREP.clearanceMargin

/** The wire legitimately passes THROUGH its own ports: barrier pairs are
    exempted for chain points within the exit run of a bind on that disc
    (tree-distance ≤ the clearance depth). Everywhere else the barrier
    applies — a wire cannot wrap back through its own node. */
/** CONTINUOUS exit exemption: the barrier of a disc the chain is bound to
    is scaled by a mask m ∈ [0,1] vanishing near the chain's own anchor on
    that disc (the wire must pass through there), ramping to 1 over one
    pitch beyond the clearance radius. Geometric (resample-proof) AND
    continuous — a binary exempt boundary was measured kicking ±19 E as
    points crossed it. The mask is part of the ENERGY (U_eff = m·U): its
    gradient carries an exact anchor-side reaction, a Newton pair inside
    the chain (the anchor index accumulates it, and the bind loop forwards
    it to the body). */
/** The exemption is a CORRIDOR along the exit ray (port normal), not a
    bubble around the anchor: the wire passes through its own disc's
    clearance zone exactly along the constrained exit run. A bubble mask
    swallowed short dangles whole (buried ∃ dots), and the position-
    dependent boost that patched it broke stencil locality (the tip's move
    re-masked Euclidean-near but topologically-far edges — measured E
    rising under 'monotone' descent). The corridor depends only on PINNED
    state (anchor, normal), so locality holds. Falloffs are one-pitch
    smoothing bands. */
const maskScratch = { m: 1, anchorIdx: -1, gx: 0, gy: 0, dTheta: 0 }

/** Mask value AND its gradients: ∂m/∂p of the winning bind's active branch
    (the anchor-side gradient is exactly the negation — a Newton pair inside
    the chain) and ∂m/∂normal for the angular branch (the corridor turns
    WITH the body; omitting this from the torque is an incomplete θ-gradient
    — the one-sided-force class). */
export function exitMaskAt(ch: WireChain, disc: ChainDisc, p: Vec2): { m: number; anchorIdx: number; gx: number; gy: number; dTheta: number } {
  const r = clearance(disc.r)
  const best = maskScratch
  best.m = 1
  best.anchorIdx = -1
  best.gx = 0
  best.gy = 0
  best.dTheta = 0
  for (const b of ch.binds) {
    if (b.body !== disc.id) continue
    const ax = ch.pts[b.idx]!.x, ay = ch.pts[b.idx]!.y
    const dvx = p.x - ax, dvy = p.y - ay
    const d = Math.hypot(dvx, dvy)
    if (d < 1e-9) {
      if (0 < best.m) { best.m = 0; best.anchorIdx = b.idx; best.gx = 0; best.gy = 0; best.dTheta = 0 }
      continue
    }
    const ux = dvx / d, uy = dvy / d
    // radial band: full exemption only within the clearance reach
    const t = (d - r) / PITCH
    const radial = Math.max(0, Math.min(1, t))
    // angular corridor: exempt only along the exit direction
    let angular = 0
    let cos = 0, nx = 0, ny = 0
    if (b.normal !== undefined) {
      nx = Math.cos(b.normal)
      ny = Math.sin(b.normal)
      cos = ux * nx + uy * ny
      angular = Math.max(0, Math.min(1, (0.8 - cos) / 0.3))
    }
    const m = Math.max(radial, angular)
    if (m < best.m) {
      best.m = m
      best.anchorIdx = b.idx
      if (radial >= angular) {
        const inBand = t > 0 && t < 1
        best.gx = inBand ? ux / PITCH : 0
        best.gy = inBand ? uy / PITCH : 0
        best.dTheta = 0
      } else {
        const inBand = angular > 0 && angular < 1
        if (inBand) {
          // ∇_p cos = (n̂ − cos·û)/d ; m = (0.8 − cos)/0.3
          best.gx = (-(nx - cos * ux) / d) / 0.3
          best.gy = (-(ny - cos * uy) / d) / 0.3
          best.dTheta = (-(ux * -ny + uy * nx)) / 0.3
        } else {
          best.gx = 0
          best.gy = 0
          best.dTheta = 0
        }
      }
    }
  }
  return best
}

/** Component split of one chain's energy (debug/trace). */
export function chainEnergyParts(ch: WireChain, discs: readonly ChainDisc[]): { tension: number; spacing: number; bend: number; barrier: number } {
  const parts = { tension: 0, spacing: 0, bend: 0, barrier: 0 }
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      parts.tension += WIREP.tension * len(sub(ch.pts[n]!, ch.pts[v]!))
    }
    parts.bend += localBend(ch, v)
    parts.barrier += localBarrier(ch, discs, v)
  }
  return parts
}

/** DISCRETIZATION-INVARIANT local terms: the functional must be a proper
    discretization of a continuum energy, or every resample changes E and
    no gate can tell physics from bookkeeping (measured: coarsening bumps
    blocked chain contraction entirely).
    Bend: ∫κ²ds → Σ turn²/arc-share. Barrier: ∫U ds → Σ m·U·arc-share. */
export function arcShare(ch: WireChain, v: number): number {
  let s = 0
  for (const n of ch.adj[v]!) s += len(sub(ch.pts[n]!, ch.pts[v]!)) / 2
  return s
}

export function localBend(ch: WireChain, v: number): number {
  if (ch.adj[v]!.length !== 2) return 0
  const a = ch.adj[v]![0]!, b = ch.adj[v]![1]!
  const pv = ch.pts[v]!, pa = ch.pts[a]!, pb = ch.pts[b]!
  const ux = pa.x - pv.x, uy = pa.y - pv.y
  const wx = pb.x - pv.x, wy = pb.y - pv.y
  const lu = Math.hypot(ux, uy), lw = Math.hypot(wx, wy)
  if (lu < 1e-9 || lw < 1e-9) return 0
  const cos = Math.max(-1, Math.min(1, (ux * wx + uy * wy) / (lu * lw)))
  const turn = Math.PI - Math.acos(cos)
  return (WIREP.bend * turn * turn) / Math.max(0.25, (lu + lw) / 2)
}

/** TUNNEL-PROOF barrier: the line integral ∫m·U ds evaluated per EDGE by
    sub-sampling at unit steps — no coarse sampling can hide a disc between
    points. (Point-sampled barriers let long segments tunnel; the always-
    accept refinement rule then "revealed" the hidden energy, +2.7 per
    event, and the release powered a permanent conveyor of the ∀-fixture.) */
const scratchNear: ChainDisc[] = []
const scratchP = { x: 0, y: 0 }

/** Per-tick cache: which discs are near each edge (keyed min*65536+max).
    The numeric differentiation and line searches re-evaluate the same
    edges 3–8× per point per tick — recomputing the reject loop each time
    was measured at ~36% of settle. Rebuilt once per chain per tick. */
export type EdgeNear = Map<number, ChainDisc[] | null>
export const edgeKey = (v: number, n: number): number => (v < n ? v * 65536 + n : n * 65536 + v)

export function buildEdgeNear(ch: WireChain, allDiscs: readonly ChainDisc[]): EdgeNear {
  const discs = reachableDiscs(ch, allDiscs)
  const out: EdgeNear = new Map()
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      const a = ch.pts[v]!, b = ch.pts[n]!
      const L = Math.hypot(b.x - a.x, b.y - a.y)
      const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2
      let near: ChainDisc[] | null = null
      for (const disc of discs) {
        // one travel-cap of slack: positions move ≤ cap within the tick
        if (Math.hypot(mx - disc.pos.x, my - disc.pos.y) < clearance(disc.r) + L / 2 + PITCH + 2 * WIREP.travelCap) {
          if (near === null) near = []
          near.push(disc)
        }
      }
      out.set(edgeKey(v, n), near)
    }
  }
  return out
}

export function edgeBarrier(ch: WireChain, discs: readonly ChainDisc[], v: number, n: number, nearHint?: readonly ChainDisc[] | null): number {
  if (nearHint === null) return 0
  const a = ch.pts[v]!, b = ch.pts[n]!
  const L = Math.hypot(b.x - a.x, b.y - a.y)
  if (L < 1e-9) return 0
  let near: readonly ChainDisc[]
  if (nearHint !== undefined) {
    near = nearHint
  } else {
    const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2
    scratchNear.length = 0
    for (const disc of discs) {
      if (Math.hypot(mx - disc.pos.x, my - disc.pos.y) < clearance(disc.r) + L / 2 + PITCH) scratchNear.push(disc)
    }
    if (scratchNear.length === 0) return 0
    near = scratchNear
  }
  const K = Math.max(1, Math.ceil(L))
  let E = 0
  for (let k = 0; k <= K; k++) {
    const t = k / K
    scratchP.x = a.x + (b.x - a.x) * t
    scratchP.y = a.y + (b.y - a.y) * t
    const w = (k === 0 || k === K ? 0.5 : 1) * (L / K)
    for (const disc of near) {
      const r = clearance(disc.r)
      const d = Math.hypot(scratchP.x - disc.pos.x, scratchP.y - disc.pos.y)
      if (d >= r) continue
      const { m } = exitMaskAt(ch, disc, scratchP)
      if (m > 0) E += m * barrierU(d, r) * w
    }
  }
  return E
}

export function localBarrier(ch: WireChain, discs: readonly ChainDisc[], v: number): number {
  let E = 0
  for (const n of ch.adj[v]!) {
    if (n > v) E += edgeBarrier(ch, discs, v, n)
  }
  return E
}

/** Complete local-stencil energy of point v: every term of E that depends
    on p_v (own bend/spacing-free/barrier plus the neighbors' terms that
    reference v through arc shares and turns). The gradient differentiates
    this; the descent line-search backtracks against it. */
/** EXACTLY the terms that depend on p_v, nothing else: bend at v and its
    neighbors, barrier on v's incident edges. (localStencilE also carries
    the neighbors' other edges — constant under moves of v; differentiating
    them is pure waste, measured at ~3× the barrier cost.) Tension is
    handled analytically by the caller. */
export function pointLocalE(ch: WireChain, discs: readonly ChainDisc[], v: number, near?: EdgeNear): number {
  let s = localBend(ch, v)
  for (const n of ch.adj[v]!) {
    s += localBend(ch, n)
    s += edgeBarrier(ch, discs, Math.min(v, n), Math.max(v, n), near?.get(edgeKey(v, n)))
  }
  return s
}

export function localStencilE(ch: WireChain, discs: readonly ChainDisc[], v: number): number {
  let s = 0
  for (const k of [v, ...ch.adj[v]!]) {
    s += localBend(ch, k)
    s += localBarrier(ch, discs, k)
  }
  for (const n of ch.adj[v]!) s += WIREP.tension * len(sub(ch.pts[n]!, ch.pts[v]!))
  return s
}

/** E_wire of one chain against the given discs. */
export function chainEnergy(ch: WireChain, allDiscs: readonly ChainDisc[]): number {
  const discs = reachableDiscs(ch, allDiscs)
  let E = 0
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      E += WIREP.tension * len(sub(ch.pts[n]!, ch.pts[v]!))
    }
    E += localBend(ch, v)
    E += localBarrier(ch, discs, v)
  }
  return E
}

/** Negative gradient of E_wire at every chain point, plus the equal-and-
    opposite barrier reactions on each disc (by id). Pure — no state writes. */
/** Discs within reach of the chain's bounding box (+ their clearance):
    everything else cannot contribute to any term — pure culling, no
    behavior change. On theory-sized diagrams this is the difference
    between minutes and hours per test file. */
export function reachableDiscs(ch: WireChain, discs: readonly ChainDisc[]): ChainDisc[] {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity
  for (const p of ch.pts) {
    minX = Math.min(minX, p.x)
    minY = Math.min(minY, p.y)
    maxX = Math.max(maxX, p.x)
    maxY = Math.max(maxY, p.y)
  }
  return discs.filter((d) => {
    const r = clearance(d.r) + PITCH
    return d.pos.x >= minX - r && d.pos.x <= maxX + r && d.pos.y >= minY - r && d.pos.y <= maxY + r
  })
}

export function chainGradient(ch: WireChain, allDiscs: readonly ChainDisc[], nearMap?: EdgeNear): { f: MVec[]; onDiscs: Map<string, MVec>; bindTorque: Map<number, number> } {
  const discs = reachableDiscs(ch, allDiscs)
  const near = nearMap ?? buildEdgeNear(ch, allDiscs)
  const f: MVec[] = ch.pts.map(() => ({ x: 0, y: 0 }))
  const onDiscs = new Map<string, MVec>()
  const bindTorque = new Map<number, number>()
  const addDisc = (id: string, x: number, y: number): void => {
    const cur = onDiscs.get(id) ?? { x: 0, y: 0 }
    onDiscs.set(id, { x: cur.x + x, y: cur.y + y })
  }
  // ---- tension: unit pull toward each neighbor (gradient of length) ----
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      const dx = ch.pts[n]!.x - ch.pts[v]!.x, dy = ch.pts[n]!.y - ch.pts[v]!.y
      const d = Math.hypot(dx, dy)
      if (d < 1e-9) continue
      f[v]!.x += (WIREP.tension * dx) / d
      f[v]!.y += (WIREP.tension * dy) / d
    }
  }
  // ---- bend: ANALYTIC 3-point gradient per degree-2 point ----
  // E = B·θ²/s̄, θ = π − acos(c), c = û·ŵ, s̄ = max(0.25, (lu+lw)/2).
  // dθ/dc = 1/sinφ; near straight (θ→0) the coefficient θ/sinφ → 1, so the
  // product stays finite (guarded at the fully-folded pole). Pinned exact
  // against finite differences of chainEnergy by the battery.
  for (let i = 0; i < ch.pts.length; i++) {
    if (ch.adj[i]!.length !== 2) continue
    const ai = ch.adj[i]![0]!, bi = ch.adj[i]![1]!
    const pi = ch.pts[i]!, pa = ch.pts[ai]!, pb = ch.pts[bi]!
    const uxv = pa.x - pi.x, uyv = pa.y - pi.y
    const wxv = pb.x - pi.x, wyv = pb.y - pi.y
    const lu = Math.hypot(uxv, uyv), lw = Math.hypot(wxv, wyv)
    if (lu < 1e-9 || lw < 1e-9) continue
    const c = Math.max(-1, Math.min(1, (uxv * wxv + uyv * wyv) / (lu * lw)))
    const phi = Math.acos(c)
    const theta = Math.PI - phi
    const sMean = (lu + lw) / 2
    const sBar = Math.max(0.25, sMean)
    const sinPhi = Math.max(Math.sin(phi), 1e-9)
    const dcax = wxv / (lu * lw) - (c * uxv) / (lu * lu)
    const dcay = wyv / (lu * lw) - (c * uyv) / (lu * lu)
    const dcbx = uxv / (lu * lw) - (c * wxv) / (lw * lw)
    const dcby = uyv / (lu * lw) - (c * wyv) / (lw * lw)
    const kC = (2 * WIREP.bend * theta) / (sBar * sinPhi)
    const kS = sMean > 0.25 ? -(WIREP.bend * theta * theta) / (sBar * sBar) : 0
    const uhx = uxv / lu, uhy = uyv / lu
    const whx = wxv / lw, why = wyv / lw
    f[ai]!.x -= kC * dcax + kS * (uhx / 2)
    f[ai]!.y -= kC * dcay + kS * (uhy / 2)
    f[bi]!.x -= kC * dcbx + kS * (whx / 2)
    f[bi]!.y -= kC * dcby + kS * (why / 2)
    f[i]!.x -= kC * (-dcax - dcbx) + kS * (-(uhx + whx) / 2)
    f[i]!.y -= kC * (-dcay - dcby) + kS * (-(uhy + why) / 2)
  }
  // ---- barrier: ANALYTIC along each owned edge — the same integral the
  // energy uses, with every dependency differentiated: the sub-point (to
  // the endpoints via 1−t / t), the mask (point side + exact anchor-side
  // negation — Newton pair — and its θ-dependence via bindTorque), the
  // disc (reaction), and the weight via L ----
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      const nearE = near.get(edgeKey(v, n))
      if (nearE === null) continue
      const a = ch.pts[v]!, b2 = ch.pts[n]!
      const ex2 = b2.x - a.x, ey2 = b2.y - a.y
      const L = Math.hypot(ex2, ey2)
      if (L < 1e-9) continue
      const ehx = ex2 / L, ehy = ey2 / L
      const K = Math.max(1, Math.ceil(L))
      for (let k = 0; k <= K; k++) {
        const t = k / K
        scratchP.x = a.x + ex2 * t
        scratchP.y = a.y + ey2 * t
        const cW = (k === 0 || k === K ? 0.5 : 1) / K
        const w = cW * L
        for (const disc of nearE ?? discs) {
          const r = clearance(disc.r)
          const dvx = scratchP.x - disc.pos.x, dvy = scratchP.y - disc.pos.y
          const d = Math.hypot(dvx, dvy)
          if (d >= r || d < 1e-9) continue
          const { m, anchorIdx, gx, gy, dTheta } = exitMaskAt(ch, disc, scratchP)
          if (m <= 0 && gx === 0 && gy === 0 && dTheta === 0) continue
          const U = barrierU(d, r)
          const G = barrierG(d, r)
          const ux = dvx / d, uy = dvy / d
          const magP = m * G * w
          f[v]!.x += magP * ux * (1 - t)
          f[v]!.y += magP * uy * (1 - t)
          f[n]!.x += magP * ux * t
          f[n]!.y += magP * uy * t
          addDisc(disc.id, -magP * ux, -magP * uy)
          if ((gx !== 0 || gy !== 0) && anchorIdx >= 0) {
            const gm = w * U
            f[v]!.x -= gm * gx * (1 - t)
            f[v]!.y -= gm * gy * (1 - t)
            f[n]!.x -= gm * gx * t
            f[n]!.y -= gm * gy * t
            f[anchorIdx]!.x += gm * gx
            f[anchorIdx]!.y += gm * gy
          }
          if (dTheta !== 0 && anchorIdx >= 0) {
            bindTorque.set(anchorIdx, (bindTorque.get(anchorIdx) ?? 0) - w * U * dTheta)
          }
          const gL = cW * m * U
          f[v]!.x += gL * ehx
          f[v]!.y += gL * ehy
          f[n]!.x -= gL * ehx
          f[n]!.y -= gL * ehy
        }
      }
    }
  }
  return { f, onDiscs, bindTorque }
}

/** One damped, trust-region descent step over the chain's FREE points
    (terminals — binds, homed, slots — are constraint-owned and skipped).
    Returns the disc reactions for the caller to apply. */
export function chainStep(ch: WireChain, discs: readonly ChainDisc[], step: number, cap: number = WIREP.travelCap, rays: Map<number, { origin: Vec2; angle: number }> | null = null): Map<string, MVec> {
  const pinned = new Set<number>()
  for (const b of ch.binds) pinned.add(b.idx)
  for (const hm of ch.homed) pinned.add(hm.idx)
  for (const s of ch.slots) pinned.add(s.idx)
  const { f, onDiscs } = chainGradient(ch, discs)
  for (let v = 0; v < ch.pts.length; v++) {
    if (pinned.has(v)) continue
    // a ray-constrained point (the perpendicular exit) descends ALONG its
    // constraint — true projected gradient, so the constraint never fights
    // the descent (a post-hoc snap would raise E every tick)
    const ray = rays?.get(v)
    if (ray !== undefined) {
      const ux = Math.cos(ray.angle), uy = Math.sin(ray.angle)
      let move = (f[v]!.x * ux + f[v]!.y * uy) * step
      move = Math.max(-cap, Math.min(cap, move))
      const cur = (ch.pts[v]!.x - ray.origin.x) * ux + (ch.pts[v]!.y - ray.origin.y) * uy
      const next = Math.max(0.5, cur + move) // never crosses back through the port
      ch.pts[v] = { x: ray.origin.x + ux * next, y: ray.origin.y + uy * next }
      continue
    }
    let dx = f[v]!.x * step, dy = f[v]!.y * step
    const d = Math.hypot(dx, dy)
    if (d > cap) {
      dx = (dx / d) * cap
      dy = (dy / d) * cap
    }
    ch.pts[v] = { x: ch.pts[v]!.x + dx, y: ch.pts[v]!.y + dy }
  }
  return onDiscs
}

/** Wire-gradient force at the PINNED points (the reaction the wire exerts on
    whatever owns the pin: node bodies at binds — including a torque lever —
    and homed ∃ bodies). Pure. */
export function pinReactions(ch: WireChain, discs: readonly ChainDisc[]): Map<number, MVec> {
  const { f } = chainGradient(ch, discs)
  const out = new Map<number, MVec>()
  for (const b of ch.binds) out.set(b.idx, f[b.idx]!)
  for (const hm of ch.homed) out.set(hm.idx, f[hm.idx]!)
  return out
}

/**
 * Discrete topology descent at junction points (degree ≥ 3): a Plateau split
 * is proposed for the tightest branch pair and ACCEPTED ONLY IF it strictly
 * lowers the chain energy (ΔE < −MERGE_MARGIN keeps hysteresis: the reverse
 * merge is accepted under the same margin, so no pair of moves can flap);
 * a collapsed interior edge merges back under the same test. At most one
 * move per call — topology relaxes over ticks like everything else.
 */
const TOPO_MARGIN = 0.05

export function topologyStep(ch: WireChain, discs: readonly ChainDisc[]): void {
  // lazy: most chains have no candidate move most ticks — don't pay a
  // full-chain energy evaluation until a move is actually about to be tried
  let E0cache: number | null = null
  const E0v = (): number => {
    if (E0cache === null) E0cache = chainEnergy(ch, discs)
    return E0cache
  }
  // SPLIT: junction of degree >= 4 sheds its tightest branch pair to a child
  for (let v = 0; v < ch.pts.length; v++) {
    if (ch.adj[v]!.length < 4) continue
    const nbrs = ch.adj[v]!
    let bi = -1, bj = -1, best = -1
    for (let i = 0; i < nbrs.length; i++) for (let j = i + 1; j < nbrs.length; j++) {
      const u = sub(ch.pts[nbrs[i]!]!, ch.pts[v]!)
      const w = sub(ch.pts[nbrs[j]!]!, ch.pts[v]!)
      const lu = len(u), lw = len(w)
      if (lu < 1e-9 || lw < 1e-9) continue
      const cos = (u.x * w.x + u.y * w.y) / (lu * lw)
      if (cos > best) { best = cos; bi = i; bj = j }
    }
    if (bi < 0) continue
    const a = nbrs[bi]!, b = nbrs[bj]!
    const mid = {
      x: (ch.pts[a]!.x + ch.pts[b]!.x) / 2,
      y: (ch.pts[a]!.y + ch.pts[b]!.y) / 2,
    }
    const dir = sub(mid, ch.pts[v]!)
    const dl = len(dir)
    if (dl < 1e-9) continue
    const w2 = ch.pts.length
    const child: Vec2 = { x: ch.pts[v]!.x + (dir.x / dl) * 0.5, y: ch.pts[v]!.y + (dir.y / dl) * 0.5 }
    // try the move, keep only if E strictly drops
    ch.pts.push(child)
    ch.adj.push([a, b, v])
    ch.adj[v] = nbrs.filter((n) => n !== a && n !== b)
    ch.adj[v]!.push(w2)
    for (const x of [a, b]) ch.adj[x] = ch.adj[x]!.map((n) => (n === v ? w2 : n))
    if (chainEnergy(ch, discs) < E0v() - TOPO_MARGIN) return
    // reject: undo
    for (const x of [a, b]) ch.adj[x] = ch.adj[x]!.map((n) => (n === w2 ? v : n))
    ch.adj[v] = nbrs
    ch.pts.pop()
    ch.adj.pop()
  }
  // MERGE: a collapsed interior edge folds back if that lowers E
  const pinnedIdx = new Set<number>()
  for (const b of ch.binds) pinnedIdx.add(b.idx)
  for (const hm of ch.homed) pinnedIdx.add(hm.idx)
  for (const s of ch.slots) pinnedIdx.add(s.idx)
  for (let v = 0; v < ch.pts.length; v++) {
    if (pinnedIdx.has(v) || ch.adj[v]!.length < 3) continue
    for (const w of [...ch.adj[v]!]) {
      if (w <= v || pinnedIdx.has(w) || ch.adj[w]!.length < 3) continue
      if (len(sub(ch.pts[w]!, ch.pts[v]!)) > 0.6) continue
      const savedV = [...ch.adj[v]!], savedW = [...ch.adj[w]!]
      ch.adj[v] = [...savedV.filter((n) => n !== w), ...savedW.filter((n) => n !== v)]
      for (const n of savedW) if (n !== v) ch.adj[n] = ch.adj[n]!.map((m) => (m === w ? v : m))
      ch.adj[w] = []
      if (chainEnergy(ch, discs) < E0v() - TOPO_MARGIN) return
      for (const n of savedW) if (n !== v) ch.adj[n] = ch.adj[n]!.map((m) => (m === v ? w : m))
      ch.adj[v] = savedV
      ch.adj[w] = savedW
    }
  }
}

/** Resample every degree-≤2 path of the tree whose segment lengths drifted
    beyond 2× the pitch (or collapsed under half): a re-parameterization of
    the same polyline — E_tension is unchanged by construction, E_bend moves
    within discretization tolerance. Junction points, binds, homed, and slot
    indices are preserved (paths are rebuilt BETWEEN structure points). */
export function resample(ch: WireChain): void {
  const structural = new Set<number>()
  for (const b of ch.binds) {
    structural.add(b.idx)
    // the ray-constrained exit point is a landmark too: its distance along
    // the ray is an equilibrium of the descent, not a sampling artifact —
    // resampling it away re-triggers forever (E bumps at the threshold)
    const nbr = ch.adj[b.idx]![0]
    if (nbr !== undefined) structural.add(nbr)
  }
  for (const hm of ch.homed) structural.add(hm.idx)
  for (const s of ch.slots) structural.add(s.idx)
  for (let v = 0; v < ch.pts.length; v++) if (ch.adj[v]!.length >= 3) structural.add(v)
  // check drift
  let needs = false
  for (let v = 0; v < ch.pts.length && !needs; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      const d = len(sub(ch.pts[n]!, ch.pts[v]!))
      // lazy triggers: the edge barrier is sub-sampled (tunnel-proof) and
      // the bend is arc-share-invariant, so coarse or dense sampling is
      // energetically honest — re-discretize only on gross drift (every
      // resample event re-excites a settling transient; measured as the
      // dominant correlate of the ∀-fixture's residual wander)
      if (d > 2 * ch.pitch || (d < ch.pitch / 2 && !structural.has(v) && !structural.has(n))) { needs = true; break }
    }
  }
  if (!needs) return
  // walk structure-to-structure paths, rebuild each at pitch
  const oldPts = ch.pts, oldAdj = ch.adj
  const map = new Map<number, number>() // old structural idx -> new idx
  const pts: Vec2[] = []
  const adj: number[][] = []
  const alloc = (p: Vec2): number => {
    pts.push({ ...p })
    adj.push([])
    return pts.length - 1
  }
  const link = (a: number, b: number): void => {
    adj[a]!.push(b)
    adj[b]!.push(a)
  }
  for (const s of structural) if (oldAdj[s]!.length > 0 || ch.binds.some((b) => b.idx === s) || ch.homed.some((h) => h.idx === s) || ch.slots.some((x) => x.idx === s)) map.set(s, alloc(oldPts[s]!))
  const visited = new Set<string>()
  for (const s of structural) {
    if (!map.has(s)) continue
    for (const first of oldAdj[s]!) {
      // walk to the next structural point
      const path: Vec2[] = [oldPts[s]!]
      let prev = s, cur = first
      while (!structural.has(cur)) {
        path.push(oldPts[cur]!)
        const next = oldAdj[cur]!.find((n) => n !== prev)
        if (next === undefined) break
        prev = cur
        cur = next
      }
      path.push(oldPts[cur]!)
      // a tree has exactly one path per structural pair: build it from the
      // lower old index only
      if (cur < s || (cur === s)) continue
      const norm = `${s}:${cur}`
      if (visited.has(norm)) continue
      visited.add(norm)
      // total length + resample count
      let L = 0
      for (let i = 1; i < path.length; i++) L += len(sub(path[i]!, path[i - 1]!))
      const k = Math.min(MAX_PATH_PTS, Math.max(1, Math.round(L / ch.pitch)))
      // arc-length interpolate k−1 interior points
      let a = map.get(s)!
      let acc = 0, seg = 1
      let segStart = path[0]!, segEnd = path[1]!
      let segLen = len(sub(segEnd, segStart))
      for (let i = 1; i < k; i++) {
        const target = (L * i) / k
        while (acc + segLen < target && seg < path.length - 1) {
          acc += segLen
          seg++
          segStart = path[seg - 1]!
          segEnd = path[seg]!
          segLen = len(sub(segEnd, segStart))
        }
        const t = segLen < 1e-9 ? 0 : (target - acc) / segLen
        const idx = alloc({ x: segStart.x + (segEnd.x - segStart.x) * t, y: segStart.y + (segEnd.y - segStart.y) * t })
        link(a, idx)
        a = idx
      }
      link(a, map.get(cur)!)
    }
  }
  ch.pts = pts
  ch.adj = adj
  const remap = (idx: number): number => map.get(idx)!
  ch.binds = ch.binds.map((b) => ({ ...b, idx: remap(b.idx) }))
  ch.homed = ch.homed.map((h) => ({ ...h, idx: remap(h.idx) }))
  ch.slots = ch.slots.map((s) => ({ ...s, idx: remap(s.idx) }))
}

