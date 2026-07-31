import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { mkEngine } from '../src/view/engine'
import { settle, settleStep, setOpDebug } from '../src/view/relax'

const p = (s: string) => parseTerm(s)
const h = new DiagramBuilder()
const a = h.termNode(h.root, p('x'))
const b = h.termNode(h.root, p('x'))
const c = h.termNode(h.root, p('x'))
h.wire(h.root, [
  { node: a, port: { kind: 'freeVar', name: 'x' } },
  { node: b, port: { kind: 'freeVar', name: 'x' } },
  { node: c, port: { kind: 'freeVar', name: 'x' } },
])
const e = mkEngine(h.build(), [])
console.log('settle used', settle(e, 2600))
setOpDebug(true)
console.log('one more frame at the false rest (debug on):')
console.log('accepted:', settleStep(e))

// One-sided probes at n0: kink minimum test (central differences lie at creases)
import { totalEnergy } from '../src/view/relax'
const n0 = e.bodies.get(a)!
const E0 = totalEnergy(e)
for (const [dx, dy] of [[0.01, 0], [-0.01, 0], [0, 0.01], [0, -0.01], [0.005, 0.001], [-0.005, -0.001]] as const) {
  const s = { ...n0.pos }
  n0.pos = { x: s.x + dx, y: s.y + dy }
  console.log(`E(n0 + (${dx},${dy})) - E0 = ${(totalEnergy(e) - E0).toFixed(5)}`)
  n0.pos = s
}
