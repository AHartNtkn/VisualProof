import type { Vec2 } from '../vec'

/**
 * FREE-SPACE ROUTING (routed-network wires, USER ruling 2026-07-24).
 * Node discs, inflated by the wire clearance, are HARD obstacles: a route is a
 * deterministic shortest path in the plane minus the open inflated discs —
 * intersection is absent from the feasible space, never an energy trade-off.
 *
 * Implementation: each inflated disc is polygonalized at K vertices with
 * circumradius r/cos(π/K) (the polygon CONTAINS the disc, so polygon-feasible
 * paths are disc-feasible); shortest paths run over the visibility graph of
 * those corners plus the two query endpoints (Dijkstra, deterministic
 * index-ordered tie-breaking). The renderer's fillets restore smoothness at
 * the corners; the router never stores curve state.
 */

/** An inflated obstacle disc (world units, clearance already folded in). */
export type Disc = { readonly c: Vec2; readonly r: number }

/** Polygonalization resolution (vertices per disc). */
export const POLY_K = 16

type Corner = { p: Vec2; disc: number }

export type FreeSpace = {
  readonly discs: readonly Disc[]
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

/** A segment is feasible iff it enters no inflated disc's interior. */
export function segmentClear(a: Vec2, b: Vec2, discs: readonly Disc[]): boolean {
  for (const D of discs) {
    if (segDist(a, b, D.c) < D.r - EPS_BLOCK) return false
  }
  return true
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
export function projectFeasible(p: Vec2, discs: readonly Disc[]): Vec2 {
  let x = p.x, y = p.y
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
export function mkFreeSpace(discs: readonly Disc[]): FreeSpace {
  const corners: Corner[] = []
  for (let di = 0; di < discs.length; di++) {
    const D = discs[di]!
    const R = D.r / Math.cos(Math.PI / POLY_K)
    for (let k = 0; k < POLY_K; k++) {
      const a = (2 * Math.PI * k) / POLY_K
      const p = { x: D.c.x + R * Math.cos(a), y: D.c.y + R * Math.sin(a) }
      if (insideAnyDisc(p, discs) >= 0) continue
      corners.push({ p, disc: di })
    }
  }
  return { discs, corners, adj: null, memo: new Map() }
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

export type Route = { readonly length: number; readonly pts: readonly Vec2[] }

/** Deterministic shortest feasible path p → q. Endpoints inside an inflated
    disc are projected to its boundary first (feasibility is the caller's
    invariant; the projection makes the router total). */
export function route(fs: FreeSpace, p0: Vec2, q0: Vec2): Route {
  const p = projectFeasible(p0, fs.discs)
  const q = projectFeasible(q0, fs.discs)
  if (segmentClear(p, q, fs.discs)) {
    return { length: Math.hypot(q.x - p.x, q.y - p.y), pts: [p, q] }
  }
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
    // no feasible path (fully enclosed) — fall back to the direct segment so the
    // router is total; the caller's feasibility invariants make this unreachable
    // in normal states, and a drawn violation is visible rather than silent.
    return { length: Math.hypot(q.x - p.x, q.y - p.y), pts: [p, q] }
  }
  const rev: Vec2[] = [q]
  for (let u = prev[Q]!; u !== -1 && u !== P; u = prev[u]!) rev.push(fs.corners[u]!.p)
  rev.push(p)
  rev.reverse()
  const out: Route = { length: dist[Q]!, pts: rev }
  fs.memo.set(key, out)
  return out
}
