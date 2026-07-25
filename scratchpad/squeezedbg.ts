import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: [-24, -24, 24, 24][i]!, y: [-6, 6, -6, 6][i]! }; bd.theta = 0 })
seedProject(e)
const pinned = new Set(rs)
for (let t = 0; t < 3000; t++) if (!settleStep(e, pinned)) break
;(globalThis as { __faceDbg?: boolean }).__faceDbg = true
console.log('final frame with face-trial debug:')
console.log('moved:', settleStep(e, pinned))
