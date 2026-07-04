/**
 * ROUND 8 · A — SOAP-FILM STEINER TREE (straight segments).
 * The k-adic line is a minimal network: free branch points of degree 3 relax
 * under uniform tension (unit pull per branch — surface tension), settling
 * at 120° (Plateau). Topology is dynamic: split/merge with hysteresis.
 * USER tweak applied: node discs repel branch points (keep-out), so
 * intersections no longer hide behind nodes.
 */
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, installDrag, mkSoapTree, relaxSoap, reshapeSoap, mergeSoap, nodeObstacles, stubEnd, terminalTangent, type SoapTree } from './multiport'
import { hobbyBezier } from '../src/view/wires'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { WireId } from '../src/kernel/diagram/diagram'

const trees = new Map<WireId, SoapTree>()

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
    for (let v = 0; v < t.pts.length; v++) {
      for (const n of t.adj[v]!) {
        if (n <= v) continue
        if (v < t.nT) {
          const term = m.terminals[v]!
          // perpendicular exit (USER law): a straight stub out of the port,
          // THEN the curve — wires never leave a node at an odd angle
          const s = t.pts[v]!
          if (term.key !== null) shapes.push({ kind: 'segment', from: term.p, to: s, stroke: st.wire, width: st.wireW, glow })
          const dir = Math.atan2(t.pts[n]!.y - s.y, t.pts[n]!.x - s.x)
          const path = hobbyBezier(s, terminalTangent(term, t.pts[n]!), t.pts[n]!, dir + Math.PI)
          shapes.push({ kind: 'bezier', from: path.from, c1: path.c1, c2: path.c2, to: path.to, stroke: st.wire, width: st.wireW, glow })
        } else shapes.push({ kind: 'segment', from: t.pts[v]!, to: t.pts[n]!, stroke: st.wire, width: st.wireW, glow })
      }
    }
    for (let v = t.nT; v < t.pts.length; v++) {
      if (t.adj[v]!.length === 0) continue
      shapes.push({ kind: 'dot', center: t.pts[v]!, rPx: 2.2, fill: st.wire })
    }
  }
  return shapes
}

boot('Round 8 · A — soap-film Steiner tree', 'free triple points settle at 120° under uniform tension; node discs now REPEL branch points (the keep-out tweak); drag nodes and watch the film re-snap', (lab) => {
  installDrag(lab)
  lab.onMutate(() => trees.clear())
  lab.toast('drag any node — branch points relax to 120° and stay clear of discs')
}, mkMultiportStart, { wires })
