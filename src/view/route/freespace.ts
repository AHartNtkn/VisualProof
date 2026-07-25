import type { Vec2 } from '../vec'

/**
 * SOFT-COST ROUTING (USER ruling 2026-07-24, amended same day: "there are no
 * explicit bans on any configurations, period — everything goes onto the
 * energy function"). Node discs are NOT impassable: a stroke through a disc
 * is representable and pays OBSTACLE_COST extra per unit of length inside;
 * leaving the frame pays FRAME_COST per unit outside. The route between two
 * points is the cheaper of (a) the DIRECT segment at its soft cost and
 * (b) the best detour over the disc-polygon visibility graph — the two
 * natural extremals of the soft metric, deterministic and memoryless. The
 * drawn stroke's TURNING is charged by the caller (network energy): hairpin
 * wraps are among the costliest configurations by construction.
 */

/** An inflated obstacle disc (world units, clearance already folded in). */
export type Disc = { readonly c: Vec2; readonly r: number }

/** Polygonalization resolution (vertices per disc). */
export const POLY_K = 16
/** Extra cost per unit of stroke length INSIDE a node disc (under-node travel
    is possible, just dear: ~4× normal distance). */
export const OBSTACLE_COST = 3
/** Cost per unit of stroke length OUTSIDE the frame (steep — the border law
    as energy, not a clamp). */
export const FRAME_COST = 30

type Corner = { p: Vec2; disc: number }

/** Optional rectangular containment (the fixed proof frame): junctions and
    route corners stay inside — nothing is drawn outside the border. */
export type Bounds = { readonly minX: number; readonly maxX: number; readonly minY: number; readonly maxY: number }

export type FreeSpace = {
  readonly discs: readonly Disc[]
  readonly bounds: Bounds | null
  /** polygon corners, disc-major, skipping corners buried inside other discs */
  readonly corners: readonly Corner[]
  /** corner↔corner visibility adjacency, built LAZILY on the first blocked
      route (unblocked scenes never pay for it) */
  adj: { j: number; d: number }[][] | null
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

/** Push a point out of every disc interior (feasibility projection for
    junction coordinates). Deterministic; at most one pass per disc in index
    order, repeated until clear (bounded by disc count). */
export function projectFeasible(p: Vec2, discs: readonly Disc[], bounds: Bounds | null = null): Vec2 {
  let x = p.x, y = p.y
  if (bounds !== null) {
    x = Math.max(bounds.minX, Math.min(bounds.maxX, x))
    y = Math.max(bounds.minY, Math.min(bounds.maxY, y))
  }
  for (let pass = 0; pass < discs.length + 1; pass++) {
    const i = insideAnyDisc({ x, y }, discs)
    if (i < 0) break
    const D = discs[i]!
    const dx = x - D.c.x, dy = y - D.c.y
    const d = Math.hypot(dx, dy)
    const ux = d < 1e-12 ? 1 : dx / d, uy = d < 1e-12 ? 0 : dy / d
    x = D.c.x + ux * (D.r + 1e-6)
    y = D.c.y + uy * (D.r + 1e-6)
  }
  return { x, y }
}

/** Build the static visibility structure over the inflated discs. */
export function mkFreeSpace(discs: readonly Disc[], bounds: Bounds | null = null): FreeSpace {
  const corners: Corner[] = []
  for (let di = 0; di < discs.length; di++) {
    const D = discs[di]!
    const R = D.r / Math.cos(Math.PI / POLY_K)
    for (let k = 0; k < POLY_K; k++) {
      const a = (2 * Math.PI * k) / POLY_K
      const p = { x: D.c.x + R * Math.cos(a), y: D.c.y + R * Math.sin(a) }
      if (insideAnyDisc(p, discs) >= 0) continue
      if (bounds !== null && (p.x < bounds.minX || p.x > bounds.maxX || p.y < bounds.minY || p.y > bounds.maxY)) continue
      corners.push({ p, disc: di })
    }
  }
  return { discs, bounds, corners, adj: null, memo: new Map() }
}

function cornerAdjacency(fs: FreeSpace): { j: number; d: number }[][] {
  if (fs.adj !== null) return fs.adj
  const corners = fs.corners
  const adj: { j: number; d: number }[][] = corners.map(() => [])
  for (let i = 0; i < corners.length; i++) {
    for (let j = i + 1; j < corners.length; j++) {
      const a = corners[i]!.p, b = corners[j]!.p
      if (!segmentClear(a, b, fs.discs)) continue
      const d = Math.hypot(a.x - b.x, a.y - b.y)
      adj[i]!.push({ j, d })
      adj[j]!.push({ j: i, d })
    }
  }
  fs.adj = adj
  return adj
}

export type Route = { readonly length: number; readonly cost: number; readonly pts: readonly Vec2[] }


/** Deterministic cheapest path p → q under the SOFT metric: the direct
    segment at its soft cost vs the best clear detour over the disc-polygon
    graph. No configuration is banned — a through-disc stroke simply pays. */
export function route(fs: FreeSpace, p: Vec2, q: Vec2): Route {
  const directLen = Math.hypot(q.x - p.x, q.y - p.y)
  const directCost = segSoftCost(p, q, fs)
  const direct: Route = { length: directLen, cost: directCost, pts: [p, q] }
  if (segmentClear(p, q, fs.discs)) return direct
  const key = `${p.x},${p.y},${q.x},${q.y}`
  const hit = fs.memo.get(key)
  if (hit !== undefined) return hit
  // Dijkstra over corners + {p, q}
  const adjacency = cornerAdjacency(fs)
  const n = fs.corners.length
  const P = n, Q = n + 1
  const dist = new Array<number>(n + 2).fill(Infinity)
  const prev = new Array<number>(n + 2).fill(-1)
  const done = new Array<boolean>(n + 2).fill(false)
  const pcon: { j: number; d: number }[] = []
  const qcon: { j: number; d: number }[] = []
  for (let i = 0; i < n; i++) {
    const c = fs.corners[i]!.p
    if (segmentClear(p, c, fs.discs)) pcon.push({ j: i, d: Math.hypot(c.x - p.x, c.y - p.y) })
    if (segmentClear(q, c, fs.discs)) qcon.push({ j: i, d: Math.hypot(c.x - q.x, c.y - q.y) })
  }
  dist[P] = 0
  for (;;) {
    // deterministic extract-min (index order breaks ties)
    let u = -1, best = Infinity
    for (let i = 0; i < n + 2; i++) if (!done[i] && dist[i]! < best) { best = dist[i]!; u = i }
    if (u < 0) break
    done[u] = true
    if (u === Q) break
    const edges = u === P ? pcon : adjacency[u]!
    for (const { j, d } of edges) {
      if (dist[u]! + d < dist[j]!) { dist[j] = dist[u]! + d; prev[j] = u }
    }
    if (u !== P) {
      // connection to Q from a corner
      const qc = qcon.find((e) => e.j === u)
      if (qc !== undefined && dist[u]! + qc.d < dist[Q]!) { dist[Q] = dist[u]! + qc.d; prev[Q] = u }
    } else {
      // p might see q around... (handled by the direct test above)
    }
  }
  if (!Number.isFinite(dist[Q]!)) {
    fs.memo.set(key, direct)
    return direct
  }
  const rev: Vec2[] = [q]
  for (let u = prev[Q]!; u !== -1 && u !== P; u = prev[u]!) rev.push(fs.corners[u]!.p)
  rev.push(p)
  rev.reverse()
  // detour cost: clear segments cost their length (+ any frame surcharge)
  let detourCost = 0
  for (let i = 0; i + 1 < rev.length; i++) detourCost += segSoftCost(rev[i]!, rev[i + 1]!, fs)
  // THE choice is by soft cost: under-disc travel wins when the detour is
  // genuinely dearer — no ban either way
  const out: Route = detourCost < directCost
    ? { length: dist[Q]!, cost: detourCost, pts: rev }
    : direct
  fs.memo.set(key, out)
  return out
}
