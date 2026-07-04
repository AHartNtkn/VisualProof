/**
 * ROUND 8 · B — FORCE-DIRECTED EDGE BUNDLING (Holten & van Wijk 2009).
 * Each leg of the k-adic line is a FLEXIBLE SPRING subdivided into control
 * points; corresponding points of sibling legs ATTRACT each other. No
 * explicit junction geometry exists at all — trunks emerge where the legs
 * choose to travel together, and re-form live as the layout's energy
 * changes. The legs still meet at one shared point (the line is one line),
 * but its position is just the bundle's own equilibrium.
 */
import { boot, mkMultiportStart, collectMultiport, basePaintExcept, installDrag } from './multiport'
import type { Engine } from '../src/view/engine'
import type { Shape, Theme } from '../src/view/paint'
import type { Vec2 } from '../src/view/vec'
import type { WireId } from '../src/kernel/diagram/diagram'

const P = 14 // control points per leg (Holten's subdivision)
const SPRING = 0.45 // smoothing spring between path neighbors
const ATTRACT = 0.06 // sibling attraction step

type Bundle = { paths: Vec2[][]; center: { x: number; y: number } }
const bundles = new Map<WireId, Bundle>()

const wires = (e: Engine, st: Theme): Shape[] => {
  const mp = collectMultiport(e)
  const skip = new Set(mp.map((m) => m.wid))
  const shapes = basePaintExcept(e, st, skip)
  const glow = st.wireGlow ? st.wire : null
  for (const m of mp) {
    const k = m.terminals.length
    let b = bundles.get(m.wid)
    if (b === undefined || b.paths.length !== k) {
      const center = { ...m.hub.pos }
      b = {
        center,
        paths: m.terminals.map((t) =>
          Array.from({ length: P + 1 }, (_, j) => ({
            x: t.p.x + ((center.x - t.p.x) * j) / P,
            y: t.p.y + ((center.y - t.p.y) * j) / P,
          }))),
      }
      bundles.set(m.wid, b)
    }
    // the shared end tracks the terminals' centroid (the line's one meeting
    // point); everything between is the bundle's own business
    const cx = m.terminals.reduce((s, t) => s + t.p.x, 0) / k
    const cy = m.terminals.reduce((s, t) => s + t.p.y, 0) / k
    b.center.x += (cx - b.center.x) * 0.2
    b.center.y += (cy - b.center.y) * 0.2
    m.terminals.forEach((t, i) => { b!.paths[i]![0] = { ...t.p } })
    for (const path of b.paths) path[P] = { ...b.center }
    for (let iter = 0; iter < 2; iter++) {
      for (let i = 0; i < k; i++) {
        const path = b.paths[i]!
        for (let j = 1; j < P; j++) {
          const p = path[j]!
          let fx = (path[j - 1]!.x + path[j + 1]!.x - 2 * p.x) * SPRING
          let fy = (path[j - 1]!.y + path[j + 1]!.y - 2 * p.y) * SPRING
          for (let i2 = 0; i2 < k; i2++) {
            if (i2 === i) continue
            const q = b.paths[i2]![j]!
            const d = Math.hypot(q.x - p.x, q.y - p.y)
            if (d < 1e-9) continue
            // Holten's electrostatic attraction, saturated near contact so
            // bundled points do not oscillate through each other
            const w = Math.min(1, 2 / d) * ATTRACT
            fx += (q.x - p.x) * w
            fy += (q.y - p.y) * w
          }
          path[j] = { x: p.x + fx, y: p.y + fy }
        }
      }
    }
    for (const path of b.paths) {
      for (let j = 0; j < P; j++) {
        shapes.push({ kind: 'segment', from: path[j]!, to: path[j + 1]!, stroke: st.wire, width: st.wireW, glow })
      }
    }
  }
  return shapes
}

boot('Round 8 · B — force-directed bundling', 'legs are flexible springs that ATTRACT each other (Holten & van Wijk): trunks emerge on their own, no junction geometry at all; drag nodes and the bundle re-forms', (lab) => {
  installDrag(lab)
  lab.onMutate(() => bundles.clear())
  lab.toast('drag any node — the legs re-bundle around the new layout')
}, mkMultiportStart, { wires })
