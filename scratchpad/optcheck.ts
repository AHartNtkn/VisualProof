import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, enableLayoutOptimization } from '../src/view/relax'
import { layoutScore } from '../src/view/optimize'
const p = (s: string) => parseTerm(s)
const b = new DiagramBuilder()
for (let i = 0; i < 4; i++) b.termNode(b.root, p('x'))
const e = mkEngine(b.build(), [])
seedProject(e)
// local-only rest first
for (let t = 0; t < 3000; t++) if (!settleStep(e)) break
const localRest = layoutScore(e)
console.log(`local rest score: ${localRest.toFixed(3)}`)
// now enable the global optimizer and keep stepping (as the app would)
enableLayoutOptimization(true)
let last = localRest
for (let t = 0; t < 2000; t++) {
  const moved = settleStep(e)
  if (t % 250 === 0) {
    const sc = layoutScore(e)
    console.log(`t=${t} score=${sc.toFixed(3)} moved=${moved}`)
    last = sc
  }
  if (!moved) { console.log(`RESTED (search exhausted) at t=${t}, score=${layoutScore(e).toFixed(3)}`); break }
}
console.log(`final: ${layoutScore(e).toFixed(3)} (local rest was ${localRest.toFixed(3)})`)
enableLayoutOptimization(false)
