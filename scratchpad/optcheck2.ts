import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, enableLayoutOptimization } from '../src/view/relax'
import { layoutScore } from '../src/view/optimize'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
seedProject(e)
for (let t = 0; t < 3000; t++) if (!settleStep(e)) break
const localRest = layoutScore(e)
const wire = e.wires.get(w)!
const pairing = () => {
  const nT = 4
  const side = (j: number) => wire.net.edges
    .filter(([u, v]) => u === nT + j || v === nT + j)
    .flatMap(([u, v]) => [u, v].filter((x) => x < nT)).sort().join('')
  return wire.net.junctions.length === 2 ? [side(0), side(1)].sort().join('|') : `${wire.net.junctions.length}j`
}
console.log(`local rest: score=${localRest.toFixed(3)} pairing=${pairing()}`)
enableLayoutOptimization(true)
for (let t = 0; t < 4000; t++) {
  const moved = settleStep(e)
  if (t % 500 === 0) console.log(`t=${t} score=${layoutScore(e).toFixed(3)} pairing=${pairing()}`)
  if (!moved) { console.log(`RESTED at t=${t}`); break }
}
console.log(`final: score=${layoutScore(e).toFixed(3)} pairing=${pairing()} (local rest ${localRest.toFixed(3)})`)
enableLayoutOptimization(false)
