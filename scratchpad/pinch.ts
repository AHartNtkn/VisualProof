import type { Vec2 } from '../src/view/vec'
import { mkFreeSpace } from '../src/view/route/freespace'
import { advanceNetwork, type WireNet } from '../src/view/route/network'
const empty = mkFreeSpace([])
let terms: Vec2[] = [{ x: -20, y: -6 }, { x: -20, y: 6 }, { x: 20, y: -6 }, { x: 20, y: 6 }]
const net: WireNet = { junctions: [{ x: -10, y: 0 }, { x: 10, y: 0 }], edges: [[0, 4], [1, 4], [2, 5], [3, 5], [4, 5]] }
for (let i = 0; i < 200; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })) break
const sep = () => net.junctions.length < 2 ? 'CONTRACTED(' + net.junctions.length + 'j)' : Math.hypot(net.junctions[1]!.x - net.junctions[0]!.x, net.junctions[1]!.y - net.junctions[0]!.y).toFixed(4)
console.log('start sep', sep())
for (let step = 0; step <= 120; step++) {
  const t = step / 120
  const w = 20 - 19.8 * t
  terms = [{ x: -w, y: -6 }, { x: -w, y: 6 }, { x: w, y: -6 }, { x: w, y: 6 }]
  advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })
  if (step % 20 === 0 || step > 110) console.log(`step ${step} w=${w.toFixed(2)} sep=${sep()} junctions=${net.junctions.length}`)
}
for (let i = 0; i < 200; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })) break
console.log('final settle:', sep(), 'junctions', net.junctions.length, 'edges', JSON.stringify(net.edges))
