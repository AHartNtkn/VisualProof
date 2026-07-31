import { mkEngine, routeObstacles, wireTerminalPoints } from '../src/view/engine'
import { settleStep, seedProject, wireEnergy, contentEnergy } from '../src/view/relax'
import { mkFreeSpace } from '../src/view/route/freespace'
import { advanceNetwork } from '../src/view/route/network'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e = mkEngine(r.diagramAt(20), r.boundaryAt(20))
seedProject(e)
for (let i = 0; i < 10; i++) settleStep(e)
let t0 = performance.now()
for (let i = 0; i < 200; i++) { wireEnergy(e); contentEnergy(e) }
console.log(`energy eval: ${((performance.now() - t0) / 200).toFixed(2)}ms`)
t0 = performance.now()
for (let i = 0; i < 5; i++) {
  const fs = mkFreeSpace(routeObstacles(e))
  for (const [, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length >= 2) advanceNetwork(w.net, terms, fs, { substeps: 20, bound: 0.55 * e.scale })
  }
}
console.log(`router pass: ${((performance.now() - t0) / 5).toFixed(1)}ms`)
t0 = performance.now()
for (let i = 0; i < 5; i++) settleStep(e)
console.log(`full frame: ${((performance.now() - t0) / 5).toFixed(1)}ms`)
