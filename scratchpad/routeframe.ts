import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e = mkEngine(r.diagramAt(20), r.boundaryAt(20))
seedProject(e)
for (let t = 0; t < 40; t++) {
  const f0 = performance.now()
  const moved = settleStep(e)
  const ms = performance.now() - f0
  if (t % 5 === 0 || !moved) console.log(`t=${t} ${ms.toFixed(1)}ms moved=${moved} E=${totalEnergy(e).toFixed(1)}`)
  if (!moved) break
}
