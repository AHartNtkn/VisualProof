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
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, installDrag, mkSoapTree, relaxSoap, reshapeSoap, mergeSoap, nodeObstacles, stubEnd, terminalTangent, type SoapTree } from './multiport'
import { hobbyBezier } from '../src/view/wires'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { WireId } from '../src/kernel/diagram/diagram'

const trees = new Map<WireId, SoapTree>()
;(window as unknown as { __r8trees: Map<WireId, SoapTree> }).__r8trees = trees
const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

/** Outgoing tangents at an internal point, CONTINUOUS in the layout: the
    junction's through-axis is its RELAXED orientation phi (state with
    inertia, not a per-frame pair choice); each branch's tangent is its own
    direction pulled toward the nearer axis side, with a blend weight
    |cos(dir − phi)| that vanishes exactly where the side choice flips —
    so no configuration can jump. */
function outTangents(t: SoapTree, v: number): Map<number, number> {
  const nbrs = t.adj[v]!
  const out = new Map<number, number>()
  const phi = t.phi[v]!
  for (const n of nbrs) {
    const dir = Math.atan2(t.pts[n]!.y - t.pts[v]!.y, t.pts[n]!.x - t.pts[v]!.x)
    const axisSide = Math.abs(wrap(phi - dir)) <= Math.PI / 2 ? phi : phi + Math.PI
    const wgt = Math.abs(Math.cos(dir - phi))
    out.set(n, dir + wrap(axisSide - dir) * wgt)
  }
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
    m.terminals.forEach((x, i) => { t!.pts[i] = stubEnd(x) })
    relaxSoap(t, obstacles, m.hub.pos)
    reshapeSoap(t)
    mergeSoap(t, obstacles, m.hub.pos)
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
        // terminal ends draw from the PORT ANCHOR (the stub end is only the
        // leaf's position in the tree's energy)
        const pv = v < t.nT ? m.terminals[v]!.p : t.pts[v]!
        const pn = n < t.nT ? m.terminals[n]!.p : t.pts[n]!
        const chord = Math.atan2(pn.y - pv.y, pn.x - pv.x)
        const tv = v < t.nT ? terminalTangent(m.terminals[v]!, pn) : clampTo(tangents.get(v)!.get(n)!, chord)
        const tn = n < t.nT ? terminalTangent(m.terminals[n]!, pv) : clampTo(tangents.get(n)!.get(v)!, chord + Math.PI)
        const path = hobbyBezier(pv, tv, pn, tn)
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
