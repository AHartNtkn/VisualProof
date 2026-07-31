import type { Vec2 } from '../vec'

/**
 * SOFT-COST ROUTING (USER ruling 2026-07-24, amended same day: "there are no
 * explicit bans on any configurations, period — everything goes onto the
 * energy function"). Node discs are NOT impassable: a stroke through a disc
 * is representable and pays OBSTACLE_COST extra per unit of length inside;
 * leaving the frame pays FRAME_COST per unit outside. The route between two
 * points is the cheaper of (a) the DIRECT segment at its soft cost and
 * (b) the best CLEAR detour — the two natural extremals of the soft metric,
 * deterministic and memoryless. The drawn stroke's TURNING is charged by the
 * caller (network energy): hairpin wraps are among the costliest by construction.
 *
 * The clear detour is a shortest path AMONG DISCS, computed on the classical
 * BITANGENT tangent graph: the geodesic is straight tangent runs between discs
 * and boundary arcs hugging them, so its only vertices are the ≤4 bitangent
 * touch points per disc pair (2 outer, 2 inner) plus the 2 tangent points from
 * each endpoint — O(D²) nodes, versus O((K·D)²) for a K-gon-per-disc corner
 * graph. That corner graph (K=16) was the ~13 ms/eval cost this replaces.
 */

/** An inflated obstacle disc (world units, clearance already folded in). */
export type Disc = { readonly c: Vec2; readonly r: number }

/** Extra cost per unit of stroke length INSIDE a node disc (under-node travel
    is possible, just dear: ~4× normal distance). */
export const OBSTACLE_COST = 3
/** Cost per unit of stroke length OUTSIDE the frame (steep — the border law
    as energy, not a clamp). */
export const FRAME_COST = 30

/** Arc output resolution: a hugging arc is DRAWN as chords no wider than this
    angular step. */
const ARC_STEP = Math.PI / 8
/** Draw-circumscription factor. The geodesic hugs the true disc boundary (radius
    r) — that is the shortest clear path and the length/cost this reports — but ANY
    inscribed chord of the r-circle dips inside it and would fail `segmentClear`
    (the behavioral contract). So the DRAWN arc rides a slightly larger circle of
    radius r·ROUTE_INFLATE, on which an ARC_STEP-wide chord is tangent to r (chord
    of circle R, half-angle ARC_STEP/2, sags to R·cos(ARC_STEP/2) = r ⇒
    ROUTE_INFLATE = 1/cos(ARC_STEP/2) ≈ 1.0196), joined to the true tangent points
    by tiny (≈0.02·r) radial jogs that the downstream clearance-tolerance
    simplification erases. Rendering only — never the routed length. */
const ROUTE_INFLATE = 1 / Math.cos(ARC_STEP / 2)

/** Optional rectangular containment (the fixed proof frame): junctions and
    route corners stay inside — nothing is drawn outside the border. */
export type Bounds = { readonly minX: number; readonly maxX: number; readonly minY: number; readonly maxY: number }

/** A tangent point on a disc's boundary circle (radius r), with its angle there. */
type TangentPt = { readonly p: Vec2; readonly disc: number; readonly ang: number }
/** A graph edge to node `to`: a straight bitangent (arc null) or a boundary arc
    (the disc it hugs, the start angle, and the signed sweep, for reconstruction). */
type Edge = { readonly to: number; readonly cost: number; readonly arc: { readonly disc: number; readonly from: number; readonly sweep: number } | null }
/** A blocked angular interval on a disc's boundary circle (start angle, length),
    where some OTHER disc overlaps it — precomputed once per disc pair. */
type Interval = { readonly s: number; readonly l: number }
/** The static tangent graph, built lazily on the first blocked route (unblocked
    scenes never pay). `adj0` holds the clear bitangent runs AND the boundary arcs
    between static touch points; `perDisc` records each disc's touch points in
    angular order with their gap clearances, so a per-query p/q tangent point
    subdivides only the one gap it lands in; `blocked` is each disc's blocked
    angular intervals, so arc clearance is interval overlap, never per-arc trig. */
type TangentGraph = {
  readonly points: readonly TangentPt[]
  readonly adj0: readonly Edge[][]
  readonly perDisc: readonly { readonly order: number[]; readonly ang: number[]; readonly gapClear: boolean[] }[]
  readonly blocked: readonly Interval[][]
}

export type FreeSpace = {
  readonly discs: readonly Disc[]
  readonly bounds: Bounds | null
  /** The static bitangent graph, built LAZILY on the first blocked route
      (unblocked scenes never pay for it). */
  tg: TangentGraph | null
  /** pure per-frame route memo (exact endpoint tuple) — acceleration only */
  readonly memo: Map<string, Route>
}

const EPS_BLOCK = 1e-9

/** Distance from segment ab to point c. */
function segDist(a: Vec2, b: Vec2, c: Vec2): number {
  const vx = b.x - a.x, vy = b.y - a.y
  const wx = c.x - a.x, wy = c.y - a.y
  const vv = vx * vx + vy * vy
  const t = vv < 1e-18 ? 0 : Math.max(0, Math.min(1, (wx * vx + wy * vy) / vv))
  return Math.hypot(a.x + vx * t - c.x, a.y + vy * t - c.y)
}

/** A segment is clear iff it enters no inflated disc's interior. */
export function segmentClear(a: Vec2, b: Vec2, discs: readonly Disc[]): boolean {
  for (const D of discs) {
    if (segDist(a, b, D.c) < D.r - EPS_BLOCK) return false
  }
  return true
}

/** Length of segment ab inside disc D (chord clipping). */
function segInsideLen(a: Vec2, b: Vec2, D: Disc): number {
  const dx = b.x - a.x, dy = b.y - a.y
  const L = Math.hypot(dx, dy)
  if (L < 1e-12) return 0
  const fx = a.x - D.c.x, fy = a.y - D.c.y
  const bq = (fx * dx + fy * dy) / L
  const c = fx * fx + fy * fy - D.r * D.r
  const disc = bq * bq - c
  if (disc <= 0) return 0
  const sq = Math.sqrt(disc)
  const t0 = Math.max(0, -bq - sq), t1 = Math.min(L, -bq + sq)
  return Math.max(0, t1 - t0)
}

/** The SOFT cost of a straight segment: length + obstacle-interior surcharge
    + outside-frame surcharge. This is THE metric; nothing is infeasible.
    (Takes any disc/bounds pair — probe evaluators measure frozen polylines
    against live obstacles without building a full FreeSpace.) */
export function segSoftCost(a: Vec2, b: Vec2, fs: { readonly discs: readonly Disc[]; readonly bounds: Bounds | null }): number {
  const L = Math.hypot(b.x - a.x, b.y - a.y)
  let cost = L
  for (const D of fs.discs) cost += OBSTACLE_COST * segInsideLen(a, b, D)
  if (fs.bounds !== null && L > 1e-12) {
    const N = 8
    let out = 0
    for (let k = 0; k <= N; k++) {
      const t = k / N
      const x = a.x + (b.x - a.x) * t, y = a.y + (b.y - a.y) * t
      if (x < fs.bounds.minX || x > fs.bounds.maxX || y < fs.bounds.minY || y > fs.bounds.maxY) out++
    }
    cost += FRAME_COST * L * (out / (N + 1))
  }
  return cost
}

/** Total turning of a polyline (radians) — the caller charges bending. */
export function polylineTurning(pts: readonly Vec2[]): number {
  let turn = 0
  for (let i = 1; i + 1 < pts.length; i++) {
    const ax = pts[i]!.x - pts[i - 1]!.x, ay = pts[i]!.y - pts[i - 1]!.y
    const bx = pts[i + 1]!.x - pts[i]!.x, by = pts[i + 1]!.y - pts[i]!.y
    const la = Math.hypot(ax, ay), lb = Math.hypot(bx, by)
    if (la < 1e-12 || lb < 1e-12) continue
    const dot = Math.max(-1, Math.min(1, (ax * bx + ay * by) / (la * lb)))
    turn += Math.acos(dot)
  }
  return turn
}

export function insideAnyDisc(p: Vec2, discs: readonly Disc[]): number {
  for (let i = 0; i < discs.length; i++) {
    const D = discs[i]!
    if (Math.hypot(p.x - D.c.x, p.y - D.c.y) < D.r - EPS_BLOCK) return i
  }
  return -1
}

export function mkFreeSpace(discs: readonly Disc[], bounds: Bounds | null = null): FreeSpace {
  return { discs, bounds, tg: null, memo: new Map() }
}

// ---- tangent-graph geometry -------------------------------------------------

const norm2pi = (a: number): number => {
  let r = a % (2 * Math.PI)
  if (r < 0) r += 2 * Math.PI
  return r
}

/** The ≤4 bitangents of two routing circles: their touch point on each disc.
    Outer (radii parallel): the tangent-line normal n satisfies d̂·n = (R1−R2)/D,
    touch = c1+R1·n, c2+R2·n. Inner (antiparallel): d̂·n = (R1+R2)/D, touch =
    c1+R1·n, c2−R2·n. Each admits two normals (±), giving 2 outer + 2 inner;
    inner exist only when the circles are separated (D ≥ R1+R2). */
function bitangents(c1: Vec2, R1: number, c2: Vec2, R2: number): { a: Vec2; b: Vec2 }[] {
  const dx = c2.x - c1.x, dy = c2.y - c1.y
  const D = Math.hypot(dx, dy)
  if (D < 1e-9) return []
  const ux = dx / D, uy = dy / D
  const out: { a: Vec2; b: Vec2 }[] = []
  const emit = (cosv: number, inner: boolean): void => {
    if (Math.abs(cosv) > 1) return
    const sinv = Math.sqrt(1 - cosv * cosv)
    for (const s of [1, -1]) {
      const nx = ux * cosv - uy * (s * sinv)
      const ny = ux * (s * sinv) + uy * cosv
      const a = { x: c1.x + R1 * nx, y: c1.y + R1 * ny }
      const b = inner
        ? { x: c2.x - R2 * nx, y: c2.y - R2 * ny }
        : { x: c2.x + R2 * nx, y: c2.y + R2 * ny }
      out.push({ a, b })
    }
  }
  emit((R1 - R2) / D, false) // outer
  emit((R1 + R2) / D, true) // inner
  return out
}

/** The two tangent points from an external point p to a routing circle (c,R),
    or none if p is not strictly outside. Right angle at the touch point ⇒ the
    touch radius makes angle acos(R/D) with the c→p direction. */
function pointTangents(p: Vec2, c: Vec2, R: number): Vec2[] {
  const dx = p.x - c.x, dy = p.y - c.y
  const D = Math.hypot(dx, dy)
  if (D <= R) return []
  const cosv = R / D, sinv = Math.sqrt(Math.max(0, 1 - cosv * cosv))
  const ux = dx / D, uy = dy / D
  const out: Vec2[] = []
  for (const s of [1, -1]) {
    const nx = ux * cosv - uy * (s * sinv)
    const ny = ux * (s * sinv) + uy * cosv
    out.push({ x: c.x + R * nx, y: c.y + R * ny })
  }
  return out
}

/** Do the CCW arcs [s1, s1+l1] and [s2, s2+l2] have INTERIOR overlap? (Tangential
    touching at an endpoint is not overlap — the blocked interval is open.) */
function arcsOverlap(s1: number, l1: number, s2: number, l2: number): boolean {
  const d = norm2pi(s2 - s1) // arc2 start, in arc1's frame (arc1 covers [0, l1])
  return d < l1 - EPS_BLOCK || d + l2 > 2 * Math.PI + EPS_BLOCK
}

/** The angular intervals where OTHER discs overlap disc `self`'s boundary circle
    (radius r) — the blocked spans, computed ONCE per disc. A disc j meets the
    circle on the OPEN interval where cos(θ − φⱼ) > K, i.e. |θ − φⱼ| < acos(K); a
    fully-covering overlap is recorded as a full turn. Exact (atan2/acos), so per-
    arc clearance is just interval overlap with no trig. */
function discBlocked(discs: readonly Disc[], self: number): Interval[] {
  const c = discs[self]!.c, rho = discs[self]!.r
  const out: Interval[] = []
  for (let j = 0; j < discs.length; j++) {
    if (j === self) continue
    const D = discs[j]!
    const ex = D.c.x - c.x, ey = D.c.y - c.y
    const E = Math.hypot(ex, ey)
    if (E < 1e-12) {
      if (D.r > rho) return [{ s: 0, l: 2 * Math.PI }] // concentric and larger: all blocked
      continue
    }
    const K = (rho * rho + E * E - D.r * D.r) / (2 * rho * E)
    if (K >= 1) continue // disc j does not reach this circle
    if (K <= -1) return [{ s: 0, l: 2 * Math.PI }] // circle entirely inside disc j
    const half = Math.acos(K)
    out.push({ s: Math.atan2(ey, ex) - half, l: 2 * half })
  }
  return out
}

/** Is the CCW arc [lo, lo+len] clear of every precomputed blocked interval? */
function arcClearI(blocked: readonly Interval[], lo: number, len: number): boolean {
  for (const iv of blocked) if (arcsOverlap(lo, len, iv.s, iv.l)) return false
  return true
}

/** The SOFT cost of a hugging arc: its arc length (it is clear by construction,
    so no obstacle term) plus the outside-frame surcharge, sampled for the frame
    check exactly as segSoftCost samples a segment. */
function arcSoftCost(c: Vec2, rho: number, from: number, sweep: number, bounds: Bounds | null): number {
  const L = rho * Math.abs(sweep)
  if (bounds === null || L < 1e-12) return L
  const N = 8
  let out = 0
  for (let k = 0; k <= N; k++) {
    const a = from + sweep * (k / N)
    const x = c.x + rho * Math.cos(a), y = c.y + rho * Math.sin(a)
    if (x < bounds.minX || x > bounds.maxX || y < bounds.minY || y > bounds.maxY) out++
  }
  return L + FRAME_COST * L * (out / (N + 1))
}

/** DRAWN samples of a hugging arc, on the circumscribed circle (radius
    r·ROUTE_INFLATE) so chords are clear of the true disc. Emits both endpoints
    (k = 0..steps) at the circumscribed radius; the caller brackets them with the
    true tangent points, giving the ≈0.02·r radial jogs. */
function arcDrawSamples(c: Vec2, r: number, from: number, sweep: number): Vec2[] {
  const rho = r * ROUTE_INFLATE
  const steps = Math.max(1, Math.ceil(Math.abs(sweep) / ARC_STEP))
  const dA = sweep / steps
  const out: Vec2[] = []
  for (let k = 0; k <= steps; k++) {
    const a = from + dA * k
    out.push({ x: c.x + rho * Math.cos(a), y: c.y + rho * Math.sin(a) })
  }
  return out
}

/** Add the two directed arc edges for a boundary arc from node a (angle `from`)
    over CCW sweep `len` on disc d (radius r). */
function linkArc(adj: Edge[][], d: number, r: number, a: number, b: number, from: number, len: number): void {
  const cost = r * len
  adj[a]!.push({ to: b, cost, arc: { disc: d, from, sweep: len } })
  adj[b]!.push({ to: a, cost, arc: { disc: d, from: from + len, sweep: -len } })
}

function buildTangentGraph(fs: FreeSpace): TangentGraph {
  const discs = fs.discs
  const points: TangentPt[] = []
  const addPt = (p: Vec2, disc: number): number => {
    points.push({ p, disc, ang: Math.atan2(p.y - discs[disc]!.c.y, p.x - discs[disc]!.c.x) })
    return points.length - 1
  }
  const seg: [number, number, number][] = []
  for (let i = 0; i < discs.length; i++) {
    const Di = discs[i]!
    for (let j = i + 1; j < discs.length; j++) {
      const Dj = discs[j]!
      for (const { a, b } of bitangents(Di.c, Di.r, Dj.c, Dj.r)) {
        // Keep a touch point ONLY when its bitangent is a clear straight run: a
        // geodesic enters/leaves a disc via a clear bitangent, so a point on no
        // clear run is never a hug endpoint. (A buried point's bitangent is
        // blocked by the disc it is buried in, so segmentClear filters it too.)
        if (!segmentClear(a, b, discs)) continue
        seg.push([addPt(a, i), addPt(b, j), Math.hypot(a.x - b.x, a.y - b.y)])
      }
    }
  }
  const adj0: Edge[][] = points.map(() => [])
  for (const [i, j, len] of seg) { adj0[i]!.push({ to: j, cost: len, arc: null }); adj0[j]!.push({ to: i, cost: len, arc: null }) }
  const blocked = discs.map((_, d) => discBlocked(discs, d))
  const perDisc = discs.map(() => ({ order: [] as number[], ang: [] as number[], gapClear: [] as boolean[] }))
  for (let n = 0; n < points.length; n++) perDisc[points[n]!.disc]!.order.push(n)
  for (let d = 0; d < discs.length; d++) {
    const pd = perDisc[d]!, D = discs[d]!
    pd.order.sort((a, b) => points[a]!.ang - points[b]!.ang || a - b)
    for (const n of pd.order) pd.ang.push(points[n]!.ang)
    if (pd.order.length < 2) continue
    for (let k = 0; k < pd.order.length; k++) {
      const a = pd.order[k]!, b = pd.order[(k + 1) % pd.order.length]!
      const len = norm2pi(pd.ang[(k + 1) % pd.order.length]! - pd.ang[k]!)
      const clear = len >= 1e-9 && arcClearI(blocked[d]!, pd.ang[k]!, len)
      pd.gapClear.push(clear)
      if (clear) linkArc(adj0, d, D.r, a, b, pd.ang[k]!, len)
    }
  }
  return { points, adj0, perDisc, blocked }
}

export type Route = { readonly length: number; readonly cost: number; readonly pts: readonly Vec2[] }

/** Binary min-heap of node indices keyed by distance, ties broken by index
    (determinism). */
class Heap {
  private ds: number[] = []
  private is: number[] = []
  get size(): number { return this.is.length }
  private less(x: number, y: number): boolean {
    return this.ds[x]! < this.ds[y]! || (this.ds[x]! === this.ds[y]! && this.is[x]! < this.is[y]!)
  }
  push(d: number, i: number): void {
    this.ds.push(d); this.is.push(i)
    let k = this.is.length - 1
    while (k > 0) {
      const par = (k - 1) >> 1
      if (!this.less(k, par)) break
      this.swap(k, par); k = par
    }
  }
  pop(): number {
    const top = this.is[0]!
    const last = this.is.length - 1
    this.swap(0, last)
    this.ds.pop(); this.is.pop()
    let k = 0
    for (;;) {
      const l = 2 * k + 1, r = l + 1
      let m = k
      if (l < this.is.length && this.less(l, m)) m = l
      if (r < this.is.length && this.less(r, m)) m = r
      if (m === k) break
      this.swap(k, m); k = m
    }
    return top
  }
  private swap(a: number, b: number): void {
    const d = this.ds[a]!; this.ds[a] = this.ds[b]!; this.ds[b] = d
    const i = this.is[a]!; this.is[a] = this.is[b]!; this.is[b] = i
  }
}

/** Deterministic cheapest path p → q under the SOFT metric: the direct segment
    at its soft cost vs the best CLEAR detour on the bitangent tangent graph.
    No configuration is banned — a through-disc stroke simply pays. */
export function route(fs: FreeSpace, p: Vec2, q: Vec2): Route {
  const directLen = Math.hypot(q.x - p.x, q.y - p.y)
  const directCost = segSoftCost(p, q, fs)
  const direct: Route = { length: directLen, cost: directCost, pts: [p, q] }
  if (segmentClear(p, q, fs.discs)) return direct
  const key = `${p.x},${p.y},${q.x},${q.y}`
  const hit = fs.memo.get(key)
  if (hit !== undefined) return hit

  const tg = fs.tg ?? (fs.tg = buildTangentGraph(fs))
  const discs = fs.discs
  const nStatic = tg.points.length

  // per-query nodes: the p/q tangent points (2 per disc from each endpoint).
  const pq: { p: Vec2; disc: number; ang: number; end: 0 | 1; seg: number }[] = []
  for (let d = 0; d < discs.length; d++) {
    const D = discs[d]!
    for (const [end, src] of [[0, p], [1, q]] as const) {
      for (const tp of pointTangents(src, D.c, D.r)) {
        // a buried tp has a blocked tangent segment, so segmentClear alone filters
        // it (no separate insideAnyDisc needed here — the hot path).
        if (!segmentClear(src, tp, discs)) continue
        pq.push({ p: tp, disc: d, ang: Math.atan2(tp.y - D.c.y, tp.x - D.c.x), end, seg: Math.hypot(src.x - tp.x, src.y - tp.y) })
      }
    }
  }
  const M = nStatic + pq.length, P = M, Q = M + 1
  const coordOf = (n: number): Vec2 => (n < nStatic ? tg.points[n]!.p : n < M ? pq[n - nStatic]!.p : n === P ? p : q)
  const angOf = (n: number): number => (n < nStatic ? tg.points[n]!.ang : pq[n - nStatic]!.ang)
  // `extra` holds ONLY the per-query edges (p/q tangent segments + arc
  // subdivisions), SPARSE by node (most of the ~O(D²) static nodes get none), so a
  // query never allocates an entry per node; the static graph is reused by adj0.
  const extra = new Map<number, Edge[]>()
  const addE = (u: number, e: Edge): void => { const a = extra.get(u); if (a !== undefined) a.push(e); else extra.set(u, [e]) }
  const addArcE = (d: number, r: number, a: number, b: number, from: number, len: number): void => {
    const cost = r * len
    addE(a, { to: b, cost, arc: { disc: d, from, sweep: len } })
    addE(b, { to: a, cost, arc: { disc: d, from: from + len, sweep: -len } })
  }
  for (let i = 0; i < pq.length; i++) {
    const node = nStatic + i, t = pq[i]!.end === 0 ? P : Q
    addE(t, { to: node, cost: pq[i]!.seg, arc: null })
    addE(node, { to: t, cost: pq[i]!.seg, arc: null })
  }
  // subdivide each disc's boundary: insert its p/q points into the static gap they
  // land in (inheriting that gap's precomputed clearance), chaining consecutively.
  const pqByDisc: number[][] = discs.map(() => [])
  for (let i = 0; i < pq.length; i++) pqByDisc[pq[i]!.disc]!.push(nStatic + i)
  for (let d = 0; d < discs.length; d++) {
    const list = pqByDisc[d]!
    if (list.length === 0) continue
    const D = discs[d]!, pd = tg.perDisc[d]!, blk = tg.blocked[d]!, n = pd.order.length
    if (n === 0) {
      // a disc with no bitangents (e.g. a lone obstacle): its p/q points form the
      // whole boundary cycle among themselves.
      const ns = [...list].sort((a, b) => angOf(a) - angOf(b) || a - b)
      if (ns.length >= 2) {
        for (let k = 0; k < ns.length; k++) {
          const a = ns[k]!, b = ns[(k + 1) % ns.length]!
          const len = norm2pi(angOf(b) - angOf(a))
          if (len >= 1e-9 && arcClearI(blk, angOf(a), len)) addArcE(d, D.r, a, b, angOf(a), len)
        }
      }
      continue
    }
    // group the disc's p/q points by the static gap they fall in (sparse — only
    // the few gaps that actually receive a point allocate).
    const byGap = new Map<number, number[]>()
    for (const node of list) {
      const a = angOf(node)
      let k = n - 1
      for (let t = 0; t < n; t++) { if (pd.ang[t]! <= a) k = t; else break }
      if (pd.ang[0]! > a) k = n - 1
      const g = byGap.get(k); if (g !== undefined) g.push(node); else byGap.set(k, [node])
    }
    for (const [k, nodesInGap] of byGap) {
      const a0 = pd.order[k]!, b0 = pd.order[(k + 1) % n]!
      const gaplen = norm2pi(pd.ang[(k + 1) % n]! - pd.ang[k]!)
      const chain = [{ node: a0, off: 0 }, ...nodesInGap.map((node) => ({ node, off: norm2pi(angOf(node) - pd.ang[k]!) })), { node: b0, off: gaplen }]
      chain.sort((x, y) => x.off - y.off || x.node - y.node)
      for (let m = 0; m + 1 < chain.length; m++) {
        const u = chain[m]!, v = chain[m + 1]!, len = v.off - u.off
        if (len < 1e-9) continue
        const from = pd.ang[k]! + u.off
        // a sub-arc of a clear static gap is clear; only a blocked gap needs re-check
        if (pd.gapClear[k]! || arcClearI(blk, from, len)) addArcE(d, D.r, u.node, v.node, from, len)
      }
    }
  }

  // A* (heap, index-tiebreak) P → Q over adj0 (static) ∪ extra (per-query). The
  // heuristic is straight-line distance to q, which is ≤ any remaining path
  // (every edge cost — straight or arc — is ≥ its chord), hence admissible and
  // consistent, so A* returns the exact shortest path while exploring only nodes
  // that lead toward q. `dist` holds the g-value; the heap key is g + h.
  const h = (n: number): number => { const c = coordOf(n); return Math.hypot(c.x - q.x, c.y - q.y) }
  const dist = new Float64Array(M + 2).fill(Infinity)
  const prev = new Int32Array(M + 2).fill(-1)
  const prevArc = new Array<Edge['arc']>(M + 2).fill(null)
  const done = new Uint8Array(M + 2)
  const heap = new Heap()
  dist[P] = 0
  heap.push(h(P), P)
  while (heap.size > 0) {
    const u = heap.pop()
    if (done[u] === 1) continue
    done[u] = 1
    if (u === Q) break
    const du = dist[u]!
    const relax = (e: Edge): void => {
      const nd = du + e.cost
      if (nd < dist[e.to]!) { dist[e.to] = nd; prev[e.to] = u; prevArc[e.to] = e.arc; heap.push(nd + h(e.to), e.to) }
    }
    if (u < nStatic) for (const e of tg.adj0[u]!) relax(e)
    const ex = extra.get(u)
    if (ex !== undefined) for (const e of ex) relax(e)
  }
  if (!Number.isFinite(dist[Q]!)) {
    fs.memo.set(key, direct)
    return direct
  }

  // reconstruct P → Q; the reported length/cost is the true GEODESIC (straight
  // bitangent runs + exact arc lengths R·Δθ), which is ≤ any polygon path in the
  // same free space; the drawn `pts` expand each arc into ARC_STEP chord samples
  // (slightly shorter as a polyline, but that is only the rendering resolution).
  const nodes: number[] = []
  for (let u = Q; u !== -1; u = prev[u]!) nodes.push(u)
  nodes.reverse()
  const pts: Vec2[] = [p]
  const push = (v: Vec2): void => {
    const last = pts[pts.length - 1]!
    if (Math.hypot(v.x - last.x, v.y - last.y) >= 1e-9) pts.push(v)
  }
  let detourLen = 0, detourCost = 0
  for (let k = 1; k < nodes.length; k++) {
    const arc = prevArc[nodes[k]!]!
    const prevPt = coordOf(nodes[k - 1]!)
    const cur = coordOf(nodes[k]!)
    if (arc !== null) {
      const D = discs[arc.disc]!
      detourLen += D.r * Math.abs(arc.sweep)
      detourCost += arcSoftCost(D.c, D.r, arc.from, arc.sweep, fs.bounds)
      for (const s of arcDrawSamples(D.c, D.r, arc.from, arc.sweep)) push(s)
      push(cur) // the true tangent endpoint — closes the radial jog off the draw circle
    } else {
      detourLen += Math.hypot(cur.x - prevPt.x, cur.y - prevPt.y)
      detourCost += segSoftCost(prevPt, cur, fs)
      push(cur)
    }
  }
  const result: Route = detourCost < directCost ? { length: detourLen, cost: detourCost, pts } : direct
  fs.memo.set(key, result)
  return result
}
