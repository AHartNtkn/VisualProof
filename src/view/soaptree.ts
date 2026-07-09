import type { Vec2 } from './vec'

/**
 * Soap-film Steiner TREE topology for a k-ary junction (recovered from the old
 * VIEW-only round-8-D machinery @ bfddd17, now the PHYSICS seed). Given the k
 * terminal points it returns the branch-point positions and the tree edges;
 * engine.ts turns those into wire-owned branch DOFs plus ordinary elastica legs,
 * so the junction IS the physics wire — no separate renderer. The edge POSITIONS
 * then relax under the normal strict descent (leg tension/bend/clearance), which
 * is what bends the edges around nodes; this builder only fixes the TOPOLOGY
 * (branch count + adjacency) and a good seed layout.
 */

const SPAWN_DIST = 1.0, MERGE_DIST = 0.3, TENSION_STEP = 0.25, COS120 = Math.cos((2 * Math.PI) / 3)

type Tree = { pts: Vec2[]; adj: number[][]; nT: number }

function relax(t: Tree): void {
  for (let iter = 0; iter < 6; iter++) {
    for (let v = t.nT; v < t.pts.length; v++) {
      let fx = 0, fy = 0
      for (const n of t.adj[v]!) {
        const dx = t.pts[n]!.x - t.pts[v]!.x, dy = t.pts[n]!.y - t.pts[v]!.y
        const d = Math.hypot(dx, dy)
        if (d < 1e-9) continue
        fx += dx / d; fy += dy / d
      }
      t.pts[v] = { x: t.pts[v]!.x + fx * TENSION_STEP, y: t.pts[v]!.y + fy * TENSION_STEP }
    }
  }
}

function reshape(t: Tree): void {
  // SPLIT: a branch point holding two branches tighter than 120° sheds them onto a new point.
  for (let v = t.nT; v < t.pts.length; v++) {
    const nbrs = t.adj[v]!
    if (nbrs.length < 4) continue
    let bi = -1, bj = -1, best = COS120
    for (let i = 0; i < nbrs.length; i++) for (let j = i + 1; j < nbrs.length; j++) {
      const a = t.pts[nbrs[i]!]!, b = t.pts[nbrs[j]!]!
      const ua = { x: a.x - t.pts[v]!.x, y: a.y - t.pts[v]!.y }
      const ub = { x: b.x - t.pts[v]!.x, y: b.y - t.pts[v]!.y }
      const la = Math.hypot(ua.x, ua.y), lb = Math.hypot(ub.x, ub.y)
      if (la < 1e-9 || lb < 1e-9) continue
      const cos = (ua.x * ub.x + ua.y * ub.y) / (la * lb)
      if (cos > best) { best = cos; bi = i; bj = j }
    }
    if (bi < 0) continue
    const a = nbrs[bi]!, b = nbrs[bj]!
    const dir = Math.atan2((t.pts[a]!.y + t.pts[b]!.y) / 2 - t.pts[v]!.y, (t.pts[a]!.x + t.pts[b]!.x) / 2 - t.pts[v]!.x)
    const w = t.pts.length
    t.pts.push({ x: t.pts[v]!.x + Math.cos(dir) * SPAWN_DIST, y: t.pts[v]!.y + Math.sin(dir) * SPAWN_DIST })
    t.adj.push([a, b, v])
    t.adj[v] = nbrs.filter((n) => n !== a && n !== b)
    t.adj[v]!.push(w)
    for (const x of [a, b]) t.adj[x] = t.adj[x]!.map((n) => (n === v ? w : n))
  }
  // MERGE: an internal edge that tension collapsed folds back into one point.
  for (let v = t.nT; v < t.pts.length; v++) {
    for (const w of [...t.adj[v]!]) {
      if (w < t.nT || w <= v) continue
      const d = Math.hypot(t.pts[w]!.x - t.pts[v]!.x, t.pts[w]!.y - t.pts[v]!.y)
      if (d >= MERGE_DIST) continue
      t.adj[v] = [...t.adj[v]!.filter((n) => n !== w), ...t.adj[w]!.filter((n) => n !== v)]
      for (const n of t.adj[w]!) if (n !== v) t.adj[n] = t.adj[n]!.map((m) => (m === w ? v : m))
      t.adj[w] = []
      return
    }
  }
}

/** The Steiner tree over k terminals: `branchPts` are the internal branch points
    (in ascending tree index); `edges` are pairs [a, b] over tree nodes, where
    0..k-1 are the terminals (in the given order) and k.. are the branch points
    (so edge index j+k refers to branchPts[j]). Degenerate/dead branch points are
    dropped and indices compacted. */
export function buildJunctionTree(terms: readonly Vec2[]): { branchPts: Vec2[]; edges: [number, number][] } {
  const nT = terms.length
  const c = { x: terms.reduce((s, p) => s + p.x, 0) / nT, y: terms.reduce((s, p) => s + p.y, 0) / nT }
  const t: Tree = {
    pts: [...terms.map((p) => ({ ...p })), { ...c }],
    adj: [...terms.map(() => [nT]), terms.map((_, i) => i)],
    nT,
  }
  for (let r = 0; r < 80; r++) { relax(t); reshape(t) }
  // compact: keep terminals + live branch points (non-empty adjacency)
  const keep: number[] = []
  const remap = new Map<number, number>()
  for (let v = 0; v < t.pts.length; v++) {
    if (v < nT) { remap.set(v, v); continue }
    if (t.adj[v]!.length === 0) continue
    remap.set(v, nT + keep.length); keep.push(v)
  }
  const branchPts = keep.map((v) => ({ ...t.pts[v]! }))
  const edges: [number, number][] = []
  for (let v = 0; v < t.pts.length; v++) {
    if (!remap.has(v)) continue
    for (const n of t.adj[v]!) {
      if (!remap.has(n) || n <= v) continue
      edges.push([remap.get(v)!, remap.get(n)!])
    }
  }
  return { branchPts, edges }
}
