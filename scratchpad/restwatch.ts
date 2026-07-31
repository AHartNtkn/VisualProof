import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e = mkEngine(r.diagramAt(20), r.boundaryAt(20))
seedProject(e)
for (let t = 0; t < 280; t++) {
  if (t >= 270) (globalThis as { __frameDbg?: boolean }).__frameDbg = true
  const moved = settleStep(e)
  if (t % 40 === 0) console.log(`t=${t} moved=${moved} E=${totalEnergy(e).toFixed(2)}`)
  if (!moved) { console.log(`REST at ${t}`); break }
}
