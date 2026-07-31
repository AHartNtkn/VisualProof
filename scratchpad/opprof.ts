import { mkEngine } from '../src/view/engine'
import { settle, settleStep, setOpProf } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e = mkEngine(r.diagramAt(20), r.boundaryAt(20))
settle(e, 50)
setOpProf(true)
console.log('=== moving frames ===')
for (let i = 0; i < 3; i++) settleStep(e)
setOpProf(false)
settle(e, 20000)
setOpProf(true)
console.log('=== at-rest frames ===')
for (let i = 0; i < 3; i++) settleStep(e)
