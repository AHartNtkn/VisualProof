/**
 * ROUND 8 · D — TRIBUTARY RENDERING ON SOAP-FILM PHYSICS (the C verdict
 * refined). C's merge LOOK was liked; its physics was rejected (per-frame
 * reconstruction jumped) and its root tail read as a dangling port. Both
 * causes are gone by construction here: the branch structure is A's relaxed
 * soap tree — continuous positions, no tails, every internal point a real
 * 3-way meet — and only the RENDERING changes: at each branch point the two
 * most-opposite branches flow through as one tangent-continuous stream
 * (production's trunk rule) while the third merges TANGENT TO THE TRUNK,
 * like a stream joining a river. Node discs repel branch points (keep-out).
 */
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, installDrag, mkSoapTree, relaxSoap, reshapeSoap, nodeObstacles, driveHub, terminalTangent, type SoapTree } from './multiport'
import { hobbyBezier } from '../src/view/wires'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { WireId } from '../src/kernel/diagram/diagram'

const trees = new Map<WireId, SoapTree>()
const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

/** Outgoing tangents at an internal point: the two most-opposite branches
    form the through-trunk (tangents u and u+π); every other branch leaves
    along whichever trunk direction it is closer to — the tributary merge. */
function outTangents(t: SoapTree, v: number): Map<number, number> {
  const nbrs = t.adj[v]!
  const dirs = nbrs.map((n) => Math.atan2(t.pts[n]!.y - t.pts[v]!.y, t.pts[n]!.x - t.pts[v]!.x))
  const out = new Map<number, number>()
  if (nbrs.length === 1) { out.set(nbrs[0]!, dirs[0]!); return out }
  let bi = 0, bj = 1, best = -Infinity
  for (let i = 0; i < dirs.length; i++) for (let j = i + 1; j < dirs.length; j++) {
    const score = -Math.abs(Math.abs(wrap(dirs[i]! - dirs[j]!)) - Math.PI)
    if (score > best) { best = score; bi = i; bj = j }
  }
  const u = Math.atan2(Math.sin(dirs[bi]!) - Math.sin(dirs[bj]!), Math.cos(dirs[bi]!) - Math.cos(dirs[bj]!))
  nbrs.forEach((n, idx) => {
    if (idx === bi) out.set(n, u)
    else if (idx === bj) out.set(n, u + Math.PI)
    else out.set(n, Math.abs(wrap(dirs[idx]! - u)) <= Math.PI / 2 ? u : u + Math.PI)
  })
  return out
}

const wires = (e: Engine, st: Theme): Shape[] => {
  const mp = collectMultiport(e)
  const skip = new Set(mp.map((m) => m.wid))
  const shapes = basePaintExcept(e, st, skip)
  const glow = st.wireGlow ? st.wire : null
  const obstacles = nodeObstacles(e)
  for (const m of mp) {
    let t = trees.get(m.wid)
    if (t === undefined || t.nT !== m.terminals.length) {
      t = mkSoapTree(m.terminals, m.hub.pos)
      trees.set(m.wid, t)
    }
    m.terminals.forEach((x, i) => { t!.pts[i] = { ...x.p } })
    relaxSoap(t, obstacles)
    reshapeSoap(t)
    driveHub(m.hub, t)
    const tangents = new Map<number, Map<number, number>>()
    for (let v = t.nT; v < t.pts.length; v++) {
      if (t.adj[v]!.length > 0) tangents.set(v, outTangents(t, v))
    }
    // a Hobby curve loops when an endpoint tangent deviates from the chord
    // by ≥ 90°; clamp internal tangents strictly inside that bound (the
    // merge look survives — near the branch point the curve still leaves
    // along the trunk)
    const MAXDEV = Math.PI / 2 - 0.15
    const clampTo = (tangent: number, chord: number): number =>
      chord + Math.max(-MAXDEV, Math.min(MAXDEV, wrap(tangent - chord)))
    for (let v = 0; v < t.pts.length; v++) {
      for (const n of t.adj[v]!) {
        if (n <= v) continue
        const chord = Math.atan2(t.pts[n]!.y - t.pts[v]!.y, t.pts[n]!.x - t.pts[v]!.x)
        const tv = v < t.nT ? terminalTangent(m.terminals[v]!, t.pts[n]!) : clampTo(tangents.get(v)!.get(n)!, chord)
        const tn = n < t.nT ? terminalTangent(m.terminals[n]!, t.pts[v]!) : clampTo(tangents.get(n)!.get(v)!, chord + Math.PI)
        const path = hobbyBezier(t.pts[v]!, tv, t.pts[n]!, tn)
        shapes.push({ kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke: st.wire, width: st.wireW, glow })
      }
    }
    for (let v = t.nT; v < t.pts.length; v++) {
      if (t.adj[v]!.length === 0) continue
      shapes.push({ kind: 'dot', center: t.pts[v]!, rPx: 1.8, fill: st.wire })
    }
  }
  return shapes
}

boot('Round 8 · D — tributaries on soap physics', 'C’s tangential merging on A’s relaxed topology: streams flow THROUGH branch points, side branches merge tangent to the trunk; no tails, no jumps; discs repel branch points', (lab) => {
  installDrag(lab)
  lab.onMutate(() => trees.clear())
  lab.toast('drag any node — confluences glide with the soap film and merge like streams')
}, mkMultiportStart, { wires })
