import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
seedProject(e)
const wire = e.wires.get(w)!
rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: [-40, -40, 40, 40][i]!, y: [-10, 10, -10, 10][i]! }; bd.theta = 0 })
const pinned = new Set(rs)
let acc = 0
for (let t = 0; t < 400; t++) {
  const moved = settleStep(e, pinned)
  if (moved) acc++
  if (t % 100 === 0 || t === 399) {
    const b0 = wire.branches[0]!, b1 = wire.branches[1]!
    console.log(`t=${t} moved=${moved} acc=${acc} E=${totalEnergy(e).toFixed(1)} b0=(${b0.x.toFixed(1)},${b0.y.toFixed(1)}) b1=(${b1.x.toFixed(1)},${b1.y.toFixed(1)}) thetas=${rs.map((id) => e.bodies.get(id)!.theta.toFixed(2)).join(',')}`)
  }
  if (!moved && t > 5) break
}
