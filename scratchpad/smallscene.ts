import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settle, settleStep } from '../src/view/relax'
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
const b = new DiagramBuilder()
const r1 = b.ref(b.root, 'plus', rel(3))
const r2 = b.ref(b.root, 'times', rel(3))
const r3 = b.ref(b.root, 'succ', rel(2))
b.wire(b.root, [
  { node: r1, port: { kind: 'arg', index: 0 } },
  { node: r2, port: { kind: 'arg', index: 0 } },
  { node: r3, port: { kind: 'arg', index: 0 } },
])
const e = mkEngine(b.build(), [])
settle(e, 30)
let t0 = performance.now(); for (let i = 0; i < 20; i++) settleStep(e)
console.log(`threeWay (6 bodies): frame(moving)=${((performance.now() - t0) / 20).toFixed(1)}ms`)
const used = settle(e, 20000)
t0 = performance.now(); for (let i = 0; i < 20; i++) settleStep(e)
console.log(`threeWay settled in ${used + 30} ticks; frame(atRest)=${((performance.now() - t0) / 20).toFixed(1)}ms`)
