import type { Vec2 } from '../vec'
import type { FreeSpace } from './freespace'
import { route } from './freespace'
import type { CurveBC, NearSpace } from './curve'
import { curveEnergy, solveEdgeCurve } from './curve'

/**
 * THE WIRE NETWORK (routed-network wires, USER ruling 2026-07-24).
 * One wire = one explicit graph over terminals (fixed per frame: port escape
 * points, boundary slots, free endpoints) and junction vertices with
 * positions and ARBITRARY degree ≥ 3. Edges are incidences only. The
 * objective is total routed length L(G,x) = Σ d_F(x_u, x_v); a zero internal
 * edge is DELETED (its endpoints identified — the actual quotient); a
 * higher-degree vertex SPLITS only along the tangent-cone partition
 * derivative of L. No curvature basins, no tangents, no winding, no
 * velocity, no adaptive memory.
 */

/** Vertex reference: 0..nT-1 are terminals (positions supplied per frame),
    nT.. are junctions (stored positions, the router's coordinates). */
export type NetEdge = readonly [number, number]

export type WireNet = {
  /** junction positions, index j ↔ vertex nT + j */
  junctions: Vec2[]
  edges: NetEdge[]
}

/** Numerically-zero length for contraction (a scale, not a metastable
    boundary: two junctions this close are one vertex). */
export const CONTRACT_TOL = 1e-3
/** Opening amplitude for an accepted split (numerically small; the solve
    grows it immediately when the split is genuinely downhill). */
export const SPLIT_EPS = 1e-2
/** First-order gain threshold for a split: descending exactly when
    ½|Σ_A u − Σ_B u| > 1; require a strict margin over 1 so ties and float
    noise never split (the derivative of the stated objective, not a tuning —
    the margin is the router's angular resolution). */
export const SPLIT_MARGIN = 1e-3

const posOf = (net: WireNet, terms: readonly Vec2[], v: number): Vec2 =>
  v < terms.length ? terms[v]! : net.junctions[v - terms.length]!

/** Material-improvement epsilon (the same law as the search's publish gate and
    the greedy descent, 55356f7): at energies of ~1e4 the double-precision ULP
    is ~1e-12, so an ABSOLUTE 1e-12 acceptance threshold accepts rounding
    noise and the walk chatters forever instead of resting (measured: frames
    never fell below ~45 ms because junctions kept "improving" by dust).
    Accepts must clear noise RELATIVE to the energy's magnitude. */
const eps = (x: number): number => 1e-9 * (Math.abs(x) + 1)

/** THE network energy: the ROD energy of every edge's DRAWN curve (USER
    ruling 2026-07-24: minimal energy curves are gentle — see route/curve.ts).
    Per edge: route the waypoint skeleton through free space, build the
    deterministic Hermite curve with the terminal boundary conditions
    (`bcs[t]` = clamped anchor+direction, null = natural end), and charge
    ∫(α + β·κ²)ds plus the soft obstacle/frame surcharges along the samples.
    This is the one wire objective — the router, the topology gates, and the
    global layout score all use exactly it. */
/** Route (the seed/side proposal) + SOLVE the drawn curve of every edge,
    handing each edge's samples to `cb` (shared by netLength and netEval). */
function forEachEdgeCurve(
  net: WireNet, terms: readonly Vec2[], fs: FreeSpace, ns: NearSpace, bcs: readonly CurveBC[], beta: number,
  cb: (pts: readonly Vec2[]) => void,
): void {
  for (const [u, v] of net.edges) {
    const pu = posOf(net, terms, u), pv = posOf(net, terms, v)
    const r = route(fs, pu, pv)
    cb(solveEdgeCurve(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, pu, pv, r.hugs, ns, beta).pts)
  }
}

export function netLength(
  net: WireNet,
  terms: readonly Vec2[],
  fs: FreeSpace,
  ns: NearSpace,
  bcs: readonly CurveBC[] = [],
  beta = 0,
): number {
  let L = 0
  forEachEdgeCurve(net, terms, fs, ns, bcs, beta, (pts) => { L += curveEnergy(pts, ns, beta) })
  return L
}

/** netLength PLUS the drawn curve segments — the walk's separation-aware gate
    needs both (the rod length of the wire and its segments, to charge separation
    against the OTHER wires). */
export function netEval(
  net: WireNet, terms: readonly Vec2[], fs: FreeSpace, ns: NearSpace, bcs: readonly CurveBC[] = [], beta = 0,
): { L: number; segs: { a: Vec2; b: Vec2 }[] } {
  let L = 0
  const segs: { a: Vec2; b: Vec2 }[] = []
  forEachEdgeCurve(net, terms, fs, ns, bcs, beta, (pts) => {
    L += curveEnergy(pts, ns, beta)
    for (let i = 0; i + 1 < pts.length; i++) segs.push({ a: pts[i]!, b: pts[i + 1]! })
  })
  return { L, segs }
}

/** Routed polyline per edge (for rendering/hit-testing). */
export function netPaths(net: WireNet, terms: readonly Vec2[], fs: FreeSpace): { edge: NetEdge; pts: readonly Vec2[] }[] {
  return net.edges.map((edge) => ({
    edge,
    pts: route(fs, posOf(net, terms, edge[0]), posOf(net, terms, edge[1])).pts,
  }))
}

/** Outward unit tangents of the routed edges at a junction: the direction of
    each incident route's FIRST segment leaving the junction. */
function junctionTangents(net: WireNet, terms: readonly Vec2[], fs: FreeSpace, j: number): { edge: number; u: Vec2 }[] {
  const nT = terms.length
  const here = net.junctions[j]!
  const out: { edge: number; u: Vec2 }[] = []
  for (let ei = 0; ei < net.edges.length; ei++) {
    const [a, b] = net.edges[ei]!
    let other: number
    if (a === nT + j) other = b
    else if (b === nT + j) other = a
    else continue
    const r = route(fs, here, posOf(net, terms, other))
    const first = r.pts.length > 1 ? r.pts[1]! : posOf(net, terms, other)
    const dx = first.x - here.x, dy = first.y - here.y
    const d = Math.hypot(dx, dy)
    out.push({ edge: ei, u: d < 1e-12 ? { x: 0, y: 0 } : { x: dx / d, y: dy / d } })
  }
  return out
}

/**
 * Fixed-topology target solve: minimize L over junction positions.
 * Weiszfeld/IRLS majorization step toward the incident routes' first
 * waypoints (obstacle-free this is exactly the Fermat–Weiszfeld iteration and
 * L is convex), each junction update projected feasible and accepted only if
 * the ACTUAL objective does not increase (strict gate with backtracking).
 * Deterministic: junction index order, fixed iteration count on convergence.
 */
export function solveTarget(net: WireNet, terms: readonly Vec2[], fs: FreeSpace, maxIters = 12): void {
  const nT = terms.length
  for (let it = 0; it < maxIters; it++) {
    let maxMove = 0
    for (let j = 0; j < net.junctions.length; j++) {
      const here = net.junctions[j]!
      // incident routes' first waypoints (the IRLS anchors). The target solve
      // is OFF-SCREEN and gate-free (Weiszfeld majorization descends on its
      // own); the WALK's strict routed gate protects every visible state.
      const anchors: { p: Vec2; d: number }[] = []
      for (const [a, b] of net.edges) {
        let other: number
        if (a === nT + j) other = b
        else if (b === nT + j) other = a
        else continue
        const r = route(fs, here, posOf(net, terms, other))
        const first = r.pts.length > 1 ? r.pts[1]! : posOf(net, terms, other)
        const d = Math.max(Math.hypot(first.x - here.x, first.y - here.y), 1e-9)
        anchors.push({ p: first, d })
      }
      if (anchors.length === 0) continue
      let wx = 0, wy = 0, ws = 0
      for (const a of anchors) { wx += a.p.x / a.d; wy += a.p.y / a.d; ws += 1 / a.d }
      const target = { x: wx / ws, y: wy / ws }
      maxMove = Math.max(maxMove, Math.hypot(target.x - here.x, target.y - here.y))
      net.junctions[j] = target
    }
    if (maxMove < 1e-4) break
  }
}

/** Contract every internal junction–junction edge of routed length below the
    tolerance: DELETE the edge, identify the endpoints. The stored result is
    one higher-degree vertex — no residual edge, tangent, or chart state. */
export function contract(net: WireNet, terms: readonly Vec2[], _fs: FreeSpace): boolean {
  const nT = terms.length
  for (let ei = 0; ei < net.edges.length; ei++) {
    const [a, b] = net.edges[ei]!
    if (a < nT || b < nT) continue
    const ja = a - nT, jb = b - nT
    const pa0 = net.junctions[ja]!, pb0 = net.junctions[jb]!
    // coincidence is Euclidean by definition (a route between coincident
    // points has zero length) — no route call needed
    if (Math.hypot(pa0.x - pb0.x, pa0.y - pb0.y) >= CONTRACT_TOL) continue
    // identify jb into ja: midpoint position, re-point edges, drop the edge and jb
    const keep = Math.min(ja, jb), drop = Math.max(ja, jb)
    const pa = net.junctions[keep]!, pb = net.junctions[drop]!
    net.junctions[keep] = { x: (pa.x + pb.x) / 2, y: (pa.y + pb.y) / 2 }
    net.edges.splice(ei, 1)
    const remap = (v: number): number => {
      if (v === nT + drop) return nT + keep
      if (v > nT + drop) return v - 1
      return v
    }
    net.edges = net.edges.map(([u, v]) => [remap(u), remap(v)] as NetEdge)
    net.junctions.splice(drop, 1)
    // drop any self-loop the identification may have produced (parallel edges
    // between the same pair collapse to one)
    net.edges = net.edges.filter(([u, v]) => u !== v)
    const seen = new Set<string>()
    net.edges = net.edges.filter(([u, v]) => {
      const k = u < v ? `${u}-${v}` : `${v}-${u}`
      if (seen.has(k)) return false
      seen.add(k)
      return true
    })
    return true
  }
  return false
}

/**
 * The principled split rule (tangent-cone derivative of L): at a junction of
 * degree k ≥ 4 with outward unit tangents u_i, a partition A|B opened along
 * d = normalize(Σ_A u − Σ_B u) descends iff ½|Σ_A u − Σ_B u| > 1. Enumerate
 * unique nontrivial partitions (each side ≥ 2 so both vertices keep degree
 * ≥ 3), take the largest positive first-order gain, open by SPLIT_EPS, and
 * keep it only if the ACTUAL routed length decreased (strict gate).
 */
export function trySplit(net: WireNet, terms: readonly Vec2[], fs: FreeSpace, ns: NearSpace, bcs: readonly CurveBC[] = [], beta = 0, gate?: (net: WireNet) => number): boolean {
  const nT = terms.length
  // the acceptance gate: the caller may supply the TRUE energy restricted to this
  // wire (rod + separation vs the other wires); default is rod length alone.
  const evalE = gate ?? ((n: WireNet): number => netLength(n, terms, fs, ns, bcs, beta))
  for (let j = 0; j < net.junctions.length; j++) {
    const inc = junctionTangents(net, terms, fs, j)
    const k = inc.length
    if (k < 4) continue
    // enumerate bipartitions by bitmask; fix edge 0 in A to kill the A/B symmetry
    let bestGain = SPLIT_MARGIN
    let bestMask = 0
    for (let mask = 1; mask < 1 << k; mask++) {
      if ((mask & 1) === 0) continue
      const sizeA = popcount(mask)
      if (sizeA < 2 || k - sizeA < 2) continue
      let sx = 0, sy = 0
      for (let i = 0; i < k; i++) {
        const s = (mask >> i) & 1 ? 1 : -1
        sx += s * inc[i]!.u.x
        sy += s * inc[i]!.u.y
      }
      const gain = 0.5 * Math.hypot(sx, sy) - 1
      if (gain > bestGain) { bestGain = gain; bestMask = mask }
    }
    if (bestMask === 0) continue
    // open the split: A stays on j, B moves to a new junction at -d·ε... per the
    // ruling, the two sides separate along ±d/2 with a connector of length ε
    let sx = 0, sy = 0
    for (let i = 0; i < k; i++) {
      const s = (bestMask >> i) & 1 ? 1 : -1
      sx += s * inc[i]!.u.x
      sy += s * inc[i]!.u.y
    }
    const dn = Math.hypot(sx, sy)
    const d = { x: sx / dn, y: sy / dn }
    const here = net.junctions[j]!
    const L0 = evalE(net)
    const snapshot: WireNet = { junctions: net.junctions.map((p) => ({ ...p })), edges: [...net.edges] }
    const jb = net.junctions.length
    net.junctions[j] = { x: here.x + (d.x * SPLIT_EPS) / 2, y: here.y + (d.y * SPLIT_EPS) / 2 }
    net.junctions.push({ x: here.x - (d.x * SPLIT_EPS) / 2, y: here.y - (d.y * SPLIT_EPS) / 2 })
    // re-point B-side edges at the new junction
    let bi = 0
    net.edges = net.edges.map(([u, v], ei) => {
      const incIdx = inc.findIndex((x) => x.edge === ei)
      if (incIdx < 0) return [u, v] as NetEdge
      const inA = ((bestMask >> incIdx) & 1) === 1
      bi++
      if (inA) return [u, v] as NetEdge
      if (u === nT + j) return [nT + jb, v] as NetEdge
      if (v === nT + j) return [u, nT + jb] as NetEdge
      return [u, v] as NetEdge
    })
    void bi
    net.edges.push([nT + j, nT + jb])
    const L1 = evalE(net)
    if (L1 < L0 - eps(L0)) return true
    net.junctions = snapshot.junctions
    net.edges = snapshot.edges
  }
  return false
}

function popcount(x: number): number {
  let c = 0
  for (let v = x; v !== 0; v >>= 1) c += v & 1
  return c
}

/** Finite-difference probe scale (drawn units) for the node descent
    (relax.operatorStep): each coordinate is probed at ±FD_PROBE, and it is the
    descent ladder's FLOOR — a trial finer than the probe cannot resolve descent
    from sensing noise, so a rung set rejected down to FD_PROBE is a proven rest.
    Homed here among the routing/descent constants; imported by the descent.
    (Wire junctions get NO such in-walk descent: they are positional DOFs, so a
    junction cusp is a barrier-separated basin the walk cannot cross without
    defeating basin hopping — the Task-9 locality result — and the search layer's
    `displaceJunction` hop owns that global move instead.) */
export const FD_PROBE = 0.02

/**
 * PRESENTATION CONTINUATION (`advanceNetwork`): target layout and visible
 * transition speed are separate operations. Solve the fixed-topology target
 * off-screen; move each visible junction toward its target by at most
 * `bound` per substep, accepting only objective-decreasing states; contract
 * and split as above. Memoryless and deterministic: an unchanged settled
 * boundary is an exact no-op. Returns whether anything changed.
 */
export function advanceNetwork(
  net: WireNet,
  terms: readonly Vec2[],
  fs: FreeSpace,
  opts: {
    substeps: number; bound: number; ns: NearSpace; bcs?: readonly CurveBC[]; beta?: number
    gate?: (net: WireNet) => number
  },
): boolean {
  const bcs = opts.bcs ?? []
  const beta = opts.beta ?? 0
  // The acceptance gate: the TRUE energy restricted to this wire's junction
  // coordinates. The default is the wire's rod length; the walk supplies rod +
  // separation-vs-other-wires, which — because the other wires are fixed while
  // this wire walks — equals ΔE_total exactly, so the strict gate makes the walk a
  // strict descent of the whole objective (no rod-vs-separation limit cycle).
  const evalE = opts.gate ?? ((n: WireNet): number => netLength(n, terms, fs, opts.ns, bcs, beta))
  let changed = false
  // the off-screen fixed-topology TARGET is solved ONCE per advance (and again
  // only after a topology change) — the substeps walk toward it under the
  // per-substep bound and the strict gate
  let target: WireNet | null = null
  let curL: number | null = null
  const resolveTargetIfNeeded = (): void => {
    if (target !== null && target.junctions.length === net.junctions.length) return
    target = { junctions: net.junctions.map((p) => ({ ...p })), edges: [...net.edges] }
    solveTarget(target, terms, fs)
  }
  for (let s2 = 0; s2 < opts.substeps; s2++) {
    let stepMoved = false
    // contraction first (Euclidean coincidence — cheap, exact); the SPLIT
    // check is routed and runs once per advance, after the walk
    let topo = false
    while (contract(net, terms, fs)) { topo = true }
    if (topo) { changed = true; stepMoved = true; target = null; curL = null }
    if (net.junctions.length > 0) {
      resolveTargetIfNeeded()
      const tgt = target!
      // Each junction's bounded step toward its target is gated INDIVIDUALLY
      // (deterministic index order): the target is a routed-LENGTH proxy
      // (Weiszfeld), the gate is the true drawn energy, and a junction already
      // resting at the energy minimum can sit a hair off its proxy target — a
      // JOINT proposal then charges that junction's uphill proxy step against
      // every other junction's real descent and wedges the whole walk
      // (measured: +1.20 from a resting junction vetoing −0.39 from a
      // displaced one). The gate stays the true energy restricted to the one
      // moved coordinate, so acceptance is exact per step.
      for (let j = 0; j < net.junctions.length; j++) {
        const p = net.junctions[j]!
        const t = tgt.junctions[j]!
        const dx = t.x - p.x, dy = t.y - p.y
        const d = Math.hypot(dx, dy)
        let took = false
        if (d >= 1e-12) {
          const step = Math.min(d, opts.bound)
          if (curL === null) curL = evalE(net)
          net.junctions[j] = { x: p.x + (dx / d) * step, y: p.y + (dy / d) * step }
          const L1 = evalE(net)
          if (L1 < curL - eps(curL)) {
            curL = L1
            took = true
            stepMoved = true
            changed = true
          } else {
            net.junctions[j] = p
          }
        }
        // The Weiszfeld target is a routed-LENGTH proxy; the energy also
        // charges bending and nearness, so a junction can stall against a
        // ridge the straight-to-target step cannot descend (measured: a
        // displaced junction froze one step in) or rest at the proxy target
        // short of the true minimum. Whenever the target step stalls, probe
        // the axes under the same bound and the same strict gate — the walk
        // is then a true coordinate descent of the one energy with the proxy
        // step as its accelerator. Probes run ONLY on stall frames, and the
        // solve memo makes repeated probes of a stable stall nearly free, so
        // accepting-target frames (the active-motion hot path) never pay.
        if (!took) {
          const h = opts.bound
          if (curL === null) curL = evalE(net)
          let bestL: number = curL
          let bestP: Vec2 | null = null
          for (const [px, py] of [[h, 0], [-h, 0], [0, h], [0, -h]] as const) {
            net.junctions[j] = { x: p.x + px, y: p.y + py }
            const L1 = evalE(net)
            if (L1 < bestL - eps(bestL)) { bestL = L1; bestP = net.junctions[j]! }
          }
          if (bestP !== null) {
            net.junctions[j] = bestP
            curL = bestL
            stepMoved = true
            changed = true
          } else {
            net.junctions[j] = p
          }
        }
      }
    }
    if (!stepMoved) break
  }
  // one split check per advance, UNCONDITIONALLY. Junctions spawn at their
  // solved optimum, so a fat junction's first advance moves nothing — a split
  // check gated on motion is unreachable from birth and the degree-6 star
  // rests forever until a user wiggles a terminal (the reported defect).
  // Splitting is part of REACHING rest: a state is only a fixed point when no
  // partition descends. At a true rest the scan is cheap (the first-order
  // tangent test fails and no gate evaluates), and the caller's rest
  // certificate then skips the whole walk on the unchanged state.
  if (trySplit(net, terms, fs, opts.ns, bcs, beta, opts.gate)) changed = true
  return changed
}
