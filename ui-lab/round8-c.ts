/**
 * ROUND 8 · C — TRIBUTARY (SPIRAL) TREE, after Buchin–Speckmann–Verbeek's
 * flow-map flux trees: branches approach the root along angle-restricted
 * spirals and merge TANGENTIALLY, like streams joining a river — every
 * confluence is C¹-smooth, no star, no kinks. The root is the line's
 * junction body (its ∃ home), so the semantic handle stays where it is.
 * Keys 1/2/3 set the spiral pitch (the paper's angle restriction) live.
 */
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, installDrag } from './multiport'
import { hobbyBezier } from '../src/view/wires'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { Vec2 } from '../src/view/vec'

let pitch = (24 * Math.PI) / 180
const MERGE_R = 0.62 // a confluence sits at this fraction of the closer branch's radius

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

type Branch = { p: Vec2; ang: number; r: number; weight: number; outTangent: number }

const wires = (e: Engine, st: Theme): Shape[] => {
  const mp = collectMultiport(e)
  const skip = new Set(mp.map((m) => m.wid))
  const shapes = basePaintExcept(e, st, skip)
  const glow = st.wireGlow ? st.wire : null
  for (const m of mp) {
    const root = m.hub.pos
    // inward spiral direction at q: toward the root, rotated by the pitch
    const spiralIn = (q: Vec2): number => Math.atan2(root.y - q.y, root.x - q.x) + pitch
    const branches: Branch[] = m.terminals.map((t) => ({
      p: t.p,
      ang: Math.atan2(t.p.y - root.y, t.p.x - root.x),
      r: Math.hypot(t.p.x - root.x, t.p.y - root.y),
      weight: 1,
      outTangent: t.tangent, // terminals leave along their port normal
    }))
    const curve = (from: Branch, to: Vec2, toOutTangent: number): void => {
      const path = hobbyBezier(from.p, from.outTangent, to, toOutTangent)
      shapes.push({ kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke: st.wire, width: st.wireW, glow })
    }
    while (branches.length > 1) {
      // merge the pair closest in angle around the root (adjacent streams)
      let bi = 0, bj = 1, best = Infinity
      for (let i = 0; i < branches.length; i++) for (let j = i + 1; j < branches.length; j++) {
        const gap = Math.abs(wrap(branches[i]!.ang - branches[j]!.ang))
        if (gap < best) { best = gap; bi = i; bj = j }
      }
      const a = branches[bi]!, b = branches[bj]!
      const rm = Math.min(a.r, b.r) * MERGE_R
      const angM = a.ang + wrap(b.ang - a.ang) * (b.weight / (a.weight + b.weight))
      const p: Vec2 = { x: root.x + Math.cos(angM) * rm, y: root.y + Math.sin(angM) * rm }
      // both streams ARRIVE against the confluence's outward spiral tangent,
      // and the merged stream departs along it — C¹ at every junction
      const out = spiralIn(p) + Math.PI
      curve(a, p, out)
      curve(b, p, out)
      shapes.push({ kind: 'dot', center: p, rPx: 1.8, fill: st.wire })
      const merged: Branch = { p, ang: angM, r: rm, weight: a.weight + b.weight, outTangent: spiralIn(p) }
      branches.splice(bj, 1)
      branches.splice(bi, 1)
      branches.push(merged)
    }
    // the last stream runs into the root — the junction body keeps its dot
    // (it is the wire's semantic handle and its ∃ home)
    const last = branches[0]!
    curve(last, root, Math.atan2(last.p.y - root.y, last.p.x - root.x))
    shapes.push({ kind: 'dot', center: root, rPx: 4.4, fill: st.paper })
    shapes.push({ kind: 'dot', center: root, rPx: 2.2, fill: st.wire })
  }
  return shapes
}

boot('Round 8 · C — tributary spiral tree', 'branches merge TANGENTIALLY along angle-restricted spirals toward the junction (flow-map flux trees) — streams joining a river; keys 1/2/3 set the spiral pitch', (lab) => {
  installDrag(lab)
  window.addEventListener('keydown', (ev) => {
    const table: Record<string, number> = { '1': 12, '2': 24, '3': 36 }
    const deg = table[ev.key]
    if (deg === undefined) return
    pitch = (deg * Math.PI) / 180
    lab.toast(`spiral pitch ${deg}°`)
  })
  lab.toast('drag any node — confluences slide along the spirals; 1/2/3 changes the pitch')
}, mkMultiportStart, { wires })
