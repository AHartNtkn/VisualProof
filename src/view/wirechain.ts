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
 *   E_wire = TENSION · Σ|segment|                      (wants to be short)
 *          + BEND · Σ turn²                            (wants to be straight)
 *          + Σ barrier(disc, point)                    (wires ↔ nodes, symmetric)
 *
 * The barrier potential is finite-depth (saturating force — the engine's
 * SOFT discipline): U(d) = BARRIER_DEPTH · (1 − d/r)² inside the disc's
 * clearance radius r, zero outside. Its gradient pushes the wire point out
 * AND the disc away with equal magnitude — callers must apply the returned
 * disc reactions, which is what makes wires push nodes.
 */

export const TENSION = 1.0
export const BEND = 0.6
/** The disc↔wire barrier's SATURATED slope. It must exceed any single
    saturated content attraction (the engine's soft cap is 0.65·18 ≈ 11.7):
    with a weaker slope an attracted disc plows straight through a wire —
    the wire yields, snaps to the disc's far side, and the cycle repeats
    forever (measured: +1…+5 E spikes, wandering bodies). 1.5× for margin;
    crowds of stacked attractions can still push through, which is physical.
    Potential: quadratic ramp over the outer half of the clearance zone,
    constant slope inside — finite everywhere, gradient bounded. */
export const BARRIER_SLOPE = 18
/** Discretization health is part of the ONE functional — but ONE-SIDED:
    a floor against segment COMPRESSION only (onset pitch/2). Tangential
    sliding is a zero mode of pure tension: points bunch up and the
    1/segment bend gradient explodes into oscillation. A symmetric rest
    length was tried and is WRONG — it makes the chain an inextensible rope
    of its birth length (tension can only coil it, never shorten it;
    measured: taut dangle ropes coiling forever, driving a slow swimmer).
    Stretch costs nothing here; tension owns shortening; resample removes
    surplus points as chains contract (its compression trigger sits at
    pitch/4, below the floor's equilibrium, so it cannot churn). */
export const SPACING = 2.0
export const spacingOnset = (pitch: number): number => pitch / 2
/** Trust region: max distance any chain point moves per tick — a shortened
    descent step still descends; drawn motion stays continuous at frame
    scale (round-8 law). */
export const WIRE_TRAVEL_CAP = 0.5
/** Sampling pitch (wu) between chain points; resample beyond 2× drift. */
export const PITCH = 2

export type ChainBind = { idx: number; body: string; key: string }
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
    const k = Math.max(1, Math.round(d / pitch))
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

/** Barrier potential: gradient ramps 0 → BARRIER_SLOPE over the outer half
    of the clearance zone, constant BARRIER_SLOPE inside. */
export function barrierU(d: number, r: number): number {
  if (d >= r) return 0
  const half = r / 2
  if (d >= half) {
    const t = (r - d) / half // 0 at rim, 1 at half depth
    return (BARRIER_SLOPE * half * t * t) / 2
  }
  return (BARRIER_SLOPE * half) / 2 + BARRIER_SLOPE * (half - d)
}

export function barrierG(d: number, r: number): number {
  if (d >= r) return 0
  const half = r / 2
  if (d >= half) return (BARRIER_SLOPE * (r - d)) / half
  return BARRIER_SLOPE
}

/** The barrier clearance radius of a disc for wire points. */
export const clearance = (r: number): number => r + 1.5

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
export function exitMask(ch: WireChain, disc: ChainDisc, v: number): { m: number; anchorIdx: number; dm: number } {
  const r = clearance(disc.r)
  let best = { m: 1, anchorIdx: -1, dm: 0 }
  for (const b of ch.binds) {
    if (b.body !== disc.id) continue
    const dvec = sub(ch.pts[v]!, ch.pts[b.idx]!)
    const d = len(dvec)
    const t = (d - r) / PITCH
    const m = Math.max(0, Math.min(1, t))
    if (m < best.m) best = { m, anchorIdx: b.idx, dm: t > 0 && t < 1 ? 1 / PITCH : 0 }
  }
  return best
}

/** Component split of one chain's energy (debug/trace). */
export function chainEnergyParts(ch: WireChain, discs: readonly ChainDisc[]): { tension: number; spacing: number; bend: number; barrier: number } {
  const parts = { tension: 0, spacing: 0, bend: 0, barrier: 0 }
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      const L = len(sub(ch.pts[n]!, ch.pts[v]!))
      parts.tension += TENSION * L
      const under = spacingOnset(ch.pitch) - L
      if (under > 0) parts.spacing += SPACING * under * under
    }
    if (ch.adj[v]!.length === 2) {
      const [a, b] = ch.adj[v]! as [number, number]
      const u = sub(ch.pts[a]!, ch.pts[v]!)
      const w = sub(ch.pts[b]!, ch.pts[v]!)
      const lu = len(u), lw = len(w)
      if (lu > 1e-9 && lw > 1e-9) {
        const cos = Math.max(-1, Math.min(1, (u.x * w.x + u.y * w.y) / (lu * lw)))
        const turn = Math.PI - Math.acos(cos)
        parts.bend += BEND * turn * turn
      }
    }
    for (const disc of discs) {
      const r = clearance(disc.r)
      const d = len(sub(ch.pts[v]!, disc.pos))
      if (d < r) {
        const { m } = exitMask(ch, disc, v)
        if (m > 0) parts.barrier += m * barrierU(d, r)
      }
    }
  }
  return parts
}

/** E_wire of one chain against the given discs. */
export function chainEnergy(ch: WireChain, discs: readonly ChainDisc[]): number {
  let E = 0
  for (let v = 0; v < ch.pts.length; v++) {
    for (const n of ch.adj[v]!) {
      if (n <= v) continue
      const L = len(sub(ch.pts[n]!, ch.pts[v]!))
      E += TENSION * L
      const under = spacingOnset(ch.pitch) - L
      if (under > 0) E += SPACING * under * under
    }
    // bend at degree-2 interior points: (π − angle between segments)²
    if (ch.adj[v]!.length === 2) {
      const [a, b] = ch.adj[v]! as [number, number]
      const u = sub(ch.pts[a]!, ch.pts[v]!)
      const w = sub(ch.pts[b]!, ch.pts[v]!)
      const lu = len(u), lw = len(w)
      if (lu > 1e-9 && lw > 1e-9) {
        const cos = Math.max(-1, Math.min(1, (u.x * w.x + u.y * w.y) / (lu * lw)))
        const turn = Math.PI - Math.acos(cos)
        E += BEND * turn * turn
      }
    }
    for (const disc of discs) {
      const r = clearance(disc.r)
      const d = len(sub(ch.pts[v]!, disc.pos))
      if (d < r) {
        const { m } = exitMask(ch, disc, v)
        if (m > 0) E += m * barrierU(d, r)
      }
    }
  }
  return E
}

/** Negative gradient of E_wire at every chain point, plus the equal-and-
    opposite barrier reactions on each disc (by id). Pure — no state writes. */
export function chainGradient(ch: WireChain, discs: readonly ChainDisc[]): { f: MVec[]; onDiscs: Map<string, MVec> } {
  const f: MVec[] = ch.pts.map(() => ({ x: 0, y: 0 }))
  const onDiscs = new Map<string, MVec>()
  const addDisc = (id: string, x: number, y: number): void => {
    const cur = onDiscs.get(id) ?? { x: 0, y: 0 }
    onDiscs.set(id, { x: cur.x + x, y: cur.y + y })
  }
  for (let v = 0; v < ch.pts.length; v++) {
    // tension + spacing: unit pull toward each neighbor (gradient of
    // length) plus the parameterization-pinning quadratic's gradient
    for (const n of ch.adj[v]!) {
      const dvec = sub(ch.pts[n]!, ch.pts[v]!)
      const d = len(dvec)
      if (d < 1e-9) continue
      const under = spacingOnset(ch.pitch) - d
      const mag = TENSION - (under > 0 ? 2 * SPACING * under : 0)
      f[v]!.x += (mag * dvec.x) / d
      f[v]!.y += (mag * dvec.y) / d
    }
    // bend: numeric gradient of the local turn terms (the analytic form is
    // long; the term only involves v and its two neighbors, so a two-sided
    // difference on those three points stays cheap and exactly matches E)
    if (ch.adj[v]!.length === 2) {
      const h = 1e-4
      const local = (): number => {
        const [a, b] = ch.adj[v]! as [number, number]
        const u = sub(ch.pts[a]!, ch.pts[v]!)
        const w = sub(ch.pts[b]!, ch.pts[v]!)
        const lu = len(u), lw = len(w)
        if (lu < 1e-9 || lw < 1e-9) return 0
        const cos = Math.max(-1, Math.min(1, (u.x * w.x + u.y * w.y) / (lu * lw)))
        const turn = Math.PI - Math.acos(cos)
        return BEND * turn * turn
      }
      const p = ch.pts[v]!
      const e0 = local()
      ch.pts[v] = { x: p.x + h, y: p.y }
      const ex = local()
      ch.pts[v] = { x: p.x, y: p.y + h }
      const ey = local()
      ch.pts[v] = p
      f[v]!.x -= (ex - e0) / h
      f[v]!.y -= (ey - e0) / h
    }
    // barrier: push out of every intruded clearance zone; equal-and-opposite
    // on the disc (this is the single term both sides differentiate)
    for (const disc of discs) {
      const r = clearance(disc.r)
      const dvec = sub(ch.pts[v]!, disc.pos)
      const d = len(dvec)
      if (d >= r || d < 1e-9) continue
      const { m, anchorIdx, dm } = exitMask(ch, disc, v)
      if (m <= 0) continue
      const U = barrierU(d, r)
      const mag = m * barrierG(d, r)
      const ux = dvec.x / d, uy = dvec.y / d
      f[v]!.x += ux * mag
      f[v]!.y += uy * mag
      addDisc(disc.id, -ux * mag, -uy * mag)
      // the mask's own gradient (transition band only): pulls the point
      // toward the anchor's exempt bubble and pushes the anchor back —
      // an internal Newton pair of the chain
      if (dm > 0 && anchorIdx >= 0) {
        const avec = sub(ch.pts[v]!, ch.pts[anchorIdx]!)
        const ad = len(avec)
        if (ad > 1e-9) {
          const gm = U * dm
          const ax = avec.x / ad, ay = avec.y / ad
          f[v]!.x -= ax * gm
          f[v]!.y -= ay * gm
          f[anchorIdx]!.x += ax * gm
          f[anchorIdx]!.y += ay * gm
        }
      }
    }
  }
  return { f, onDiscs }
}

/** One damped, trust-region descent step over the chain's FREE points
    (terminals — binds, homed, slots — are constraint-owned and skipped).
    Returns the disc reactions for the caller to apply. */
export function chainStep(ch: WireChain, discs: readonly ChainDisc[], step: number, cap: number = WIRE_TRAVEL_CAP, rays: Map<number, { origin: Vec2; angle: number }> | null = null): Map<string, MVec> {
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
  const E0 = chainEnergy(ch, discs)
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
    if (chainEnergy(ch, discs) < E0 - TOPO_MARGIN) { debugCounts.topoSplit++; return }
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
      if (chainEnergy(ch, discs) < E0 - TOPO_MARGIN) { debugCounts.topoMerge++; return }
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
/** debug counter (trace tests only) */
export const debugCounts = { resample: 0, resampleReverted: 0, topoSplit: 0, topoMerge: 0 }

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
      if (d > 2 * ch.pitch || (d < ch.pitch / 4 && !structural.has(v) && !structural.has(n))) { needs = true; break }
    }
  }
  if (!needs) return
  debugCounts.resample++
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
      const k = Math.max(1, Math.round(L / ch.pitch))
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

/** Resample under the discrete-move discipline: a re-parameterization must
    not raise the energy (rebuilding a COMPRESSED path to fewer points
    concentrates turn angles and can raise E_bend — such rebuilds are
    rejected; extra resolution is harmless, a coarser lie is not). */
export function resampleGated(ch: WireChain, discs: readonly ChainDisc[]): void {
  const saved = {
    pts: ch.pts.map((p) => ({ ...p })),
    adj: ch.adj.map((a) => [...a]),
    binds: ch.binds.map((b) => ({ ...b })),
    homed: ch.homed.map((h) => ({ ...h })),
    slots: ch.slots.map((s) => ({ ...s })),
  }
  const before = chainEnergy(ch, discs)
  resample(ch)
  if (chainEnergy(ch, discs) > before + 1e-6) {
    debugCounts.resampleReverted++
    ch.pts = saved.pts
    ch.adj = saved.adj
    ch.binds = saved.binds
    ch.homed = saved.homed
    ch.slots = saved.slots
  }
}
