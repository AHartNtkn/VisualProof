/**
 * ROUND 8 · A — SOAP-FILM STEINER TREE.
 * The k-adic line is a minimal network: free branch points of degree 3 relax
 * under uniform tension (every incident branch pulls with the SAME force, a
 * unit vector — surface tension), so junctions settle at 120° (Plateau).
 * Topology is dynamic: a branch point crowded below 120° sheds a pair of
 * branches into a new child point; a collapsed internal edge merges back —
 * the tree re-forms as you drag nodes, exactly like a soap film re-snapping.
 * Spawn/merge distances are a hysteresis pair (spawn at 1.0, merge below
 * 0.3): they must be separated or the topology flaps every frame.
 */
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, entryCurve, installDrag } from './multiport'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { Vec2 } from '../src/view/vec'
import type { WireId } from '../src/kernel/diagram/diagram'

type Tree = { pts: Vec2[]; adj: number[][]; nT: number }
const trees = new Map<WireId, Tree>()

const SPAWN_DIST = 1.0
const MERGE_DIST = 0.3
const TENSION_STEP = 0.25
const COS120 = Math.cos((2 * Math.PI) / 3)

function relax(t: Tree): void {
  for (let iter = 0; iter < 6; iter++) {
    for (let v = t.nT; v < t.pts.length; v++) {
      let fx = 0, fy = 0
      for (const n of t.adj[v]!) {
        const dx = t.pts[n]!.x - t.pts[v]!.x, dy = t.pts[n]!.y - t.pts[v]!.y
        const d = Math.hypot(dx, dy)
        if (d < 1e-9) continue
        fx += dx / d
        fy += dy / d
      }
      t.pts[v] = { x: t.pts[v]!.x + fx * TENSION_STEP, y: t.pts[v]!.y + fy * TENSION_STEP }
    }
  }
}

function reshape(t: Tree): void {
  // SPLIT: a branch point holding two branches tighter than 120° sheds them
  // into a child (only when it would keep degree ≥ 3, so every internal
  // point stays a proper Plateau triple point or better)
  for (let v = t.nT; v < t.pts.length; v++) {
    const nbrs = t.adj[v]!
    if (nbrs.length < 4) continue
    // the tightest pair (largest cos) narrower than 120° (cos > cos 120°)
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
    const dir = Math.atan2(
      (t.pts[a]!.y + t.pts[b]!.y) / 2 - t.pts[v]!.y,
      (t.pts[a]!.x + t.pts[b]!.x) / 2 - t.pts[v]!.x,
    )
    const w = t.pts.length
    t.pts.push({ x: t.pts[v]!.x + Math.cos(dir) * SPAWN_DIST, y: t.pts[v]!.y + Math.sin(dir) * SPAWN_DIST })
    t.adj.push([a, b, v])
    t.adj[v] = nbrs.filter((n) => n !== a && n !== b)
    t.adj[v]!.push(w)
    for (const x of [a, b]) t.adj[x] = t.adj[x]!.map((n) => (n === v ? w : n))
  }
  // MERGE: an internal edge that tension collapsed folds its two points back
  // into one (the soap film's topology change in the other direction)
  for (let v = t.nT; v < t.pts.length; v++) {
    for (const w of [...t.adj[v]!]) {
      if (w < t.nT || w <= v) continue
      const d = Math.hypot(t.pts[w]!.x - t.pts[v]!.x, t.pts[w]!.y - t.pts[v]!.y)
      if (d >= MERGE_DIST) continue
      t.adj[v] = [...t.adj[v]!.filter((n) => n !== w), ...t.adj[w]!.filter((n) => n !== v)]
      for (const n of t.adj[w]!) if (n !== v) t.adj[n] = t.adj[n]!.map((m) => (m === w ? v : m))
      t.adj[w] = []
      return // indices shift logically; next frame continues
    }
  }
}

const wires = (e: Engine, st: Theme): Shape[] => {
  const mp = collectMultiport(e)
  const skip = new Set(mp.map((m) => m.wid))
  const shapes = basePaintExcept(e, st, skip)
  const glow = st.wireGlow ? st.wire : null
  for (const m of mp) {
    let t = trees.get(m.wid)
    if (t === undefined || t.nT !== m.terminals.length) {
      const pts = m.terminals.map((x) => ({ ...x.p }))
      pts.push({ ...m.hub.pos })
      t = { pts, adj: [...m.terminals.map(() => [m.terminals.length]), m.terminals.map((_, i) => i)], nT: m.terminals.length }
      trees.set(m.wid, t)
    }
    m.terminals.forEach((x, i) => { t!.pts[i] = { ...x.p } })
    relax(t)
    reshape(t)
    for (let v = 0; v < t.pts.length; v++) {
      for (const n of t.adj[v]!) {
        if (n <= v) continue
        if (v < t.nT) shapes.push(entryCurve(m.terminals[v]!, t.pts[n]!, st.wire, st.wireW, glow))
        else shapes.push({ kind: 'segment', from: t.pts[v]!, to: t.pts[n]!, stroke: st.wire, width: st.wireW, glow })
      }
    }
    for (let v = t.nT; v < t.pts.length; v++) {
      if (t.adj[v]!.length === 0) continue
      shapes.push({ kind: 'dot', center: t.pts[v]!, rPx: 2.2, fill: st.wire })
    }
  }
  return shapes
}

boot('Round 8 · A — soap-film Steiner tree', 'the k-adic line is a MINIMAL NETWORK: free triple points settle at 120° under uniform tension; drag nodes and watch the film re-snap its topology', (lab) => {
  installDrag(lab)
  lab.onMutate(() => trees.clear())
  lab.toast('drag any node — branch points relax to 120° and split/merge like a soap film')
}, mkMultiportStart, { wires })
