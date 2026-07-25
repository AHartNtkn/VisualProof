import { mkEngine } from '../src/view/engine'
import { settle, settleStep } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
for (const [thm, k] of [['plusComm', 20], ['succShiftS', 48]] as const) {
  const r = mkReplay(thm, bootCtx)
  const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
  // mid-settle frames (the moving regime): time frames 50..60
  settle(e, 50)
  let t0 = performance.now(); for (let i = 0; i < 10; i++) settleStep(e)
  const moving = (performance.now() - t0) / 10
  settle(e, 20000)
  t0 = performance.now(); for (let i = 0; i < 10; i++) settleStep(e)
  const atRest = (performance.now() - t0) / 10
  console.log(`${thm}@${k}: frame(moving)=${moving.toFixed(1)}ms frame(atRest)=${atRest.toFixed(1)}ms`)
}
