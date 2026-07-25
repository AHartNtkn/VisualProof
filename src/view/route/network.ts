import type { Vec2 } from '../vec'
import type { FreeSpace } from './freespace'
import { route, polylineTurning } from './freespace'

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

/** Bending weight: cost per radian of TURNING in a drawn stroke. Calibration:
    a 180° hairpin (π rad) costs ≈ 25 length units ≈ several node diameters —
    among the costliest configurations a wire can be in (USER ruling
    2026-07-24), so wraps and doubling-back are crushed while gentle detours
    stay cheap. */
export const BEND_COST = 8

/** THE network energy: soft routed cost (length + through-disc + out-of-frame
    surcharges) plus BEND_COST × total turning of each DRAWN stroke. A
    terminal-incident stroke is drawn stub + route (+ stub), so the turning
    includes the bend where the fixed stub meets the routed path — the port
    hairpin is charged, not free (USER ruling 2026-07-24: a 180° hairpin is
    among the costliest configurations; the energy charges what is drawn).
    `stubs[t]` is the fixed anchor behind terminal t, null where the terminal
    has none (a free end dot). This is the one wire objective — the router,
    the topology gates, and the global layout score all use exactly it. */
export function netLength(
  net: WireNet,
  terms: readonly Vec2[],
  fs: FreeSpace,
  stubs: readonly (Vec2 | null)[] = [],
): number {
  let L = 0
  for (const [u, v] of net.edges) {
    const r = route(fs, posOf(net, terms, u), posOf(net, terms, v))
    const su = u < stubs.length ? stubs[u]! : null
    const sv = v < stubs.length ? stubs[v]! : null
    const turn = su === null && sv === null
      ? polylineTurning(r.pts)
      : polylineTurning([...(su !== null ? [su] : []), ...r.pts, ...(sv !== null ? [sv] : [])])
    L += r.cost + BEND_COST * turn
  }
  return L
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
export function trySplit(net: WireNet, terms: readonly Vec2[], fs: FreeSpace, stubs: readonly (Vec2 | null)[] = []): boolean {
  const nT = terms.length
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
    const L0 = netLength(net, terms, fs, stubs)
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
    const L1 = netLength(net, terms, fs, stubs)
    if (L1 < L0 - 1e-12) return true
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
  opts: { substeps: number; bound: number; stubs?: readonly (Vec2 | null)[] },
): boolean {
  const stubs = opts.stubs ?? []
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
      const proposal = net.junctions.map((p, j) => {
        const t = tgt.junctions[j]!
        const dx = t.x - p.x, dy = t.y - p.y
        const d = Math.hypot(dx, dy)
        if (d < 1e-12) return p
        const step = Math.min(d, opts.bound)
        return { x: p.x + (dx / d) * step, y: p.y + (dy / d) * step }
      })
      const anyProposed = proposal.some((p, j) => p.x !== net.junctions[j]!.x || p.y !== net.junctions[j]!.y)
      if (anyProposed) {
        if (curL === null) curL = netLength(net, terms, fs, stubs)
        const before = net.junctions
        net.junctions = proposal
        const L1 = netLength(net, terms, fs, stubs)
        if (L1 < curL - 1e-12) {
          curL = L1
          stepMoved = true
          changed = true
        } else {
          net.junctions = before
        }
      }
    }
    if (!stepMoved) break
  }
  // one routed split check per advance, only when something changed (splits
  // are rare; when one fires the next advance's walk grows it under the gates;
  // at rest nothing scans — the state is already a gated fixed point)
  if (changed) trySplit(net, terms, fs, stubs)
  return changed
}
