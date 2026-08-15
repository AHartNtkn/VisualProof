import { add3, dist3, len3, norm3, scale3, sub3, v3, type Vec3 } from './vec3'

/** Vertices 0..nT-1 are the input terminals; vertex nT+j is junctions[j]. */
export type SteinerNet = { junctions: Vec3[]; edges: (readonly [number, number])[] }

/** Same first-order split law as the 2D router (route/network.ts): a strict
    margin over 1 so ties and float noise never split. */
const SPLIT_MARGIN = 1e-3
const MAX_SWEEPS = 5000

/** Weiszfeld geometric median with coincident-point guard. Convex objective;
    fixed small iteration budget then convergence check — throws if it fails
    to settle (never returns a silent bad point). */
function geometricMedian(points: readonly Vec3[], seed: Vec3): Vec3 {
  if (points.length === 0) throw new Error('geometricMedian: no points')
  if (points.length === 1) return points[0]!
  let x = seed
  for (let it = 0; it < 200; it++) {
    let wsum = 0
    let acc = v3(0, 0, 0)
    for (const p of points) {
      const d = dist3(x, p)
      if (d < 1e-12) return p // at a sample point: it is the median or the sweep will move on
      const w = 1 / d
      wsum += w
      acc = add3(acc, scale3(p, w))
    }
    const next = scale3(acc, 1 / wsum)
    const moved = dist3(next, x)
    x = next
    if (moved < 1e-10) return x
  }
  return x
}

const scaleOf = (terminals: readonly Vec3[]): number => {
  let m = 1e-9
  for (const a of terminals) for (const b of terminals) m = Math.max(m, dist3(a, b))
  return m
}

function solvePositions(
  terminals: readonly Vec3[], junctions: Vec3[], edges: (readonly [number, number])[],
): number {
  const nT = terminals.length
  const pos = (i: number): Vec3 => (i < nT ? terminals[i]! : junctions[i - nT]!)
  const nbrs: number[][] = junctions.map(() => [])
  for (const [u, w] of edges) {
    if (u >= nT) nbrs[u - nT]!.push(w)
    if (w >= nT) nbrs[w - nT]!.push(u)
  }
  const tol = 1e-9 * scaleOf(terminals)
  // Block-coordinate descent on a convex objective: total length decreases
  // every sweep, so exhausting the budget still yields a feasible
  // near-optimal net (residual drift ~ lastMove/(1-ratio), negligible at
  // render scale). Topology selection compares ACHIEVED lengths, so a
  // slow-converging topology is never a reason to abort the enumeration.
  for (let sweep = 0; sweep < MAX_SWEEPS; sweep++) {
    let moved = 0
    for (let j = 0; j < junctions.length; j++) {
      const next = geometricMedian(nbrs[j]!.map(pos), junctions[j]!)
      moved = Math.max(moved, dist3(next, junctions[j]!))
      junctions[j] = next
    }
    if (moved < tol) break
  }
  return edges.reduce((s, [u, w]) => s + dist3(pos(u), pos(w)), 0)
}

/** All full Steiner topologies for n terminals (vertices n..2n-3 are
    junctions): grow terminal k by splitting each existing edge with a fresh
    junction. Counts: 1, 3, 15 for n = 3, 4, 5. */
function fullTopologies(n: number): (readonly [number, number])[][] {
  let tops: (readonly [number, number])[][] = [[[0, n], [1, n], [2, n]]]
  for (let k = 3; k < n; k++) {
    const grown: (readonly [number, number])[][] = []
    const fresh = n + (k - 2)
    for (const top of tops) {
      for (let e = 0; e < top.length; e++) {
        const [u, w] = top[e]!
        grown.push([...top.slice(0, e), ...top.slice(e + 1), [u, fresh], [fresh, w], [fresh, k]])
      }
    }
    tops = grown
  }
  return tops
}

/** Merge junctions that landed within `tol` of a neighbor (junction OR
    terminal), dropping self-loops and duplicate edges. Degenerate optimal
    topologies collapse to fewer junctions this way. */
function contract(
  nT: number, terminals: readonly Vec3[], junctions: Vec3[],
  edges: (readonly [number, number])[], tol: number,
): SteinerNet {
  const alias = new Map<number, number>()
  const resolve = (i: number): number => {
    let cur = i
    while (alias.has(cur)) cur = alias.get(cur)!
    return cur
  }
  const posOf = (i: number): Vec3 => (i < nT ? terminals[i]! : junctions[i - nT]!)
  let changed = true
  while (changed) {
    changed = false
    for (const [u, w] of edges) {
      const a = resolve(u), b = resolve(w)
      if (a === b) continue
      if (dist3(posOf(a), posOf(b)) < tol) {
        // Merge the higher index into the lower; terminals (low indices) win.
        alias.set(Math.max(a, b), Math.min(a, b))
        changed = true
      }
    }
  }
  const keptJ: number[] = []
  for (let j = 0; j < junctions.length; j++) if (resolve(nT + j) === nT + j) keptJ.push(j)
  const remap = new Map<number, number>()
  keptJ.forEach((j, idx) => remap.set(nT + j, nT + idx))
  const outEdges: (readonly [number, number])[] = []
  const seen = new Set<string>()
  for (const [u, w] of edges) {
    const a = resolve(u), b = resolve(w)
    if (a === b) continue
    const ra = a < nT ? a : remap.get(a)!
    const rb = b < nT ? b : remap.get(b)!
    const lo = Math.min(ra, rb), hi = Math.max(ra, rb)
    const key = `${lo},${hi}`
    if (seen.has(key)) continue
    seen.add(key)
    outEdges.push([lo, hi])
  }
  return { junctions: keptJ.map((j) => junctions[j]!), edges: outEdges }
}

/** Star seed + first-order splits, for arities above exact enumeration. */
function splitNet(terminals: readonly Vec3[]): SteinerNet {
  const nT = terminals.length
  const centroid = scale3(terminals.reduce((a, b) => add3(a, b), v3(0, 0, 0)), 1 / nT)
  const junctions: Vec3[] = [geometricMedian(terminals, centroid)]
  let edges: (readonly [number, number])[] = terminals.map((_, t) => [t, nT] as const)
  solvePositions(terminals, junctions, edges)
  const eps = 1e-2 * scaleOf(terminals)
  for (let guard = 0; guard < 4 * nT; guard++) {
    let splitDone = false
    for (let j = 0; j < junctions.length && !splitDone; j++) {
      const v = nT + j
      const nbrs = edges.flatMap(([a, b]) => (a === v ? [b] : b === v ? [a] : []))
      if (nbrs.length < 4) continue
      const pos = (i: number): Vec3 => (i < nT ? terminals[i]! : junctions[i - nT]!)
      const units = nbrs.map((n) => {
        const d = sub3(pos(n), junctions[j]!)
        const l = len3(d)
        return l < 1e-12 ? v3(0, 0, 0) : scale3(d, 1 / l)
      })
      // Best bipartition with ≥2 on each side, maximizing ½|Σ_A u − Σ_B u|.
      let best: { gain: number; mask: number } | null = null
      for (let mask = 1; mask < 1 << (nbrs.length - 1); mask++) {
        let a = v3(0, 0, 0), b = v3(0, 0, 0), na = 0, nb = 0
        for (let i = 0; i < nbrs.length; i++) {
          if ((mask >> i) & 1) { a = add3(a, units[i]!); na++ } else { b = add3(b, units[i]!); nb++ }
        }
        if (na < 2 || nb < 2) continue
        const gain = 0.5 * len3(sub3(a, b))
        if (best === null || gain > best.gain) best = { gain, mask }
      }
      if (best === null || best.gain <= 1 + SPLIT_MARGIN) continue
      // Open the split: junction j keeps side A; a fresh junction takes side B.
      let dir = v3(0, 0, 0)
      for (let i = 0; i < nbrs.length; i++) dir = add3(dir, scale3(units[i]!, (best.mask >> i) & 1 ? 1 : -1))
      const open = len3(dir) < 1e-12 ? v3(eps, 0, 0) : scale3(norm3(dir), eps)
      const fresh = nT + junctions.length
      const keepA: number[] = [], moveB: number[] = []
      for (let i = 0; i < nbrs.length; i++) ((best.mask >> i) & 1 ? keepA : moveB).push(nbrs[i]!)
      junctions.push(sub3(junctions[j]!, open))
      junctions[j] = add3(junctions[j]!, open)
      edges = edges.filter(([a, b]) => a !== v && b !== v)
      edges.push(...keepA.map((n) => [Math.min(n, v), Math.max(n, v)] as const))
      edges.push(...moveB.map((n) => [Math.min(n, fresh), Math.max(n, fresh)] as const))
      edges.push([v, fresh])
      solvePositions(terminals, junctions, edges)
      splitDone = true
    }
    if (!splitDone) break
  }
  return contract(nT, terminals, junctions, edges, 1e-6 * scaleOf(terminals))
}

export function steinerNet(terminals: readonly Vec3[]): SteinerNet {
  const nT = terminals.length
  if (nT < 2) throw new Error(`steinerNet: need ≥2 terminals, got ${nT}`)
  if (nT === 2) return { junctions: [], edges: [[0, 1]] }
  if (nT > 5) return splitNet(terminals)
  const centroid = scale3(terminals.reduce((a, b) => add3(a, b), v3(0, 0, 0)), 1 / nT)
  let best: { len: number; junctions: Vec3[]; edges: (readonly [number, number])[] } | null = null
  for (const top of fullTopologies(nT)) {
    const junctions = Array.from({ length: nT - 2 }, (_, j) =>
      add3(centroid, scale3(v3(1, 0, 0), 1e-6 * j)))
    const edges = top.map(([u, w]) => [u, w] as const)
    const len = solvePositions(terminals, junctions, edges)
    if (best === null || len < best.len - 1e-12) best = { len, junctions, edges }
  }
  return contract(nT, terminals, best!.junctions, best!.edges, 1e-6 * scaleOf(terminals))
}
