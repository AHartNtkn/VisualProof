import { mkEngine } from '../src/view/engine'
import { settle, settleStep, opCounters } from '../src/view/relax'
import { mkReplay } from '../src/app/replay'
import { bootFixture } from '../tests/app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const r = mkReplay('plusComm', bootCtx)
const e = mkEngine(r.diagramAt(20), r.boundaryAt(20))
settle(e, 50)
opCounters()
const t0 = performance.now()
for (let i = 0; i < 5; i++) settleStep(e)
const total = (performance.now() - t0) / 5
const c = opCounters()
console.log(`frame=${total.toFixed(1)}ms localE: ${(c.n / 5).toFixed(0)} calls/frame, ${(c.localMs / 5).toFixed(1)}ms/frame (avg ${(c.localMs / c.n * 1000).toFixed(0)}µs/call); contentE=${(c.contentMs / 5).toFixed(1)}ms/frame`)
