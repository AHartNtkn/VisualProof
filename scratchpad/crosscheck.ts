// TWO crossed wires (diagonal pairing across a square): with the separation
// term the local solver and/or optimizer must uncross them.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, enableLayoutOptimization } from '../src/view/relax'
import { layoutScore } from '../src/view/optimize'
import { legPaths } from '../src/view/wires'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
// diagonal wiring: n0—n3 and n1—n2 (crossed when nodes sit on square corners in index order)
b.wire(b.root, [{ node: rs[0]!, port: { kind: 'arg' as const, index: 0 } }, { node: rs[3]!, port: { kind: 'arg' as const, index: 0 } }])
b.wire(b.root, [{ node: rs[1]!, port: { kind: 'arg' as const, index: 0 } }, { node: rs[2]!, port: { kind: 'arg' as const, index: 0 } }])
const e = mkEngine(b.build(), [])
// force the crossed corner arrangement
const P = [[-8, -8], [8, -8], [-8, 8], [8, 8]]
rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: P[i]![0]!, y: P[i]![1]! }; bd.theta = 0 })
seedProject(e)
const crossings = (): number => {
  const paths = legPaths(e)
  let n = 0
  for (let i = 0; i < paths.length; i++) for (let j = i + 1; j < paths.length; j++) {
    if (paths[i]!.wid === paths[j]!.wid) continue
    for (let a = 0; a + 1 < paths[i]!.pts.length; a++) for (let c = 0; c + 1 < paths[j]!.pts.length; c++) {
      const p1 = paths[i]!.pts[a]!, p2 = paths[i]!.pts[a + 1]!, p3 = paths[j]!.pts[c]!, p4 = paths[j]!.pts[c + 1]!
      const d = (p2.x - p1.x) * (p4.y - p3.y) - (p2.y - p1.y) * (p4.x - p3.x)
      if (Math.abs(d) < 1e-12) continue
      const t = ((p3.x - p1.x) * (p4.y - p3.y) - (p3.y - p1.y) * (p4.x - p3.x)) / d
      const u = ((p3.x - p1.x) * (p2.y - p1.y) - (p3.y - p1.y) * (p2.x - p1.x)) / d
      if (t > 0 && t < 1 && u > 0 && u < 1) n++
    }
  }
  return n
}
for (let t = 0; t < 3000; t++) if (!settleStep(e)) break
console.log(`local rest: score=${layoutScore(e).toFixed(3)} crossings=${crossings()}`)
enableLayoutOptimization(true)
for (let t = 0; t < 20000; t++) {
  const moved = settleStep(e)
  if (t % 2000 === 0) console.log(`t=${t} score=${layoutScore(e).toFixed(3)} crossings=${crossings()}`)
  if (!moved) { console.log(`RESTED at t=${t}`); break }
}
console.log(`final: score=${layoutScore(e).toFixed(3)} crossings=${crossings()}`)
enableLayoutOptimization(false)
