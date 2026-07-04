import { it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep, wireEnergy } from '../../src/view/relax'
import { debugCounts } from '../../src/view/wirechain'

for (const combo of [
  { name: 'FULL', flags: { __noWireBind: false, __noWireHomed: false, __noWireDisc: false, __noResample: false, __freezeTip: false } },
]) it(`WALK forallShape ${combo.name}`, () => {
  Object.assign(globalThis, combo.flags)
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const r1 = b.ref(cut, 'lt', 2), r2 = b.ref(cut, 'gt', 2)
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
  ])
  const e = mkEngine(b.build(), [])
  settle(e, 2600)
  for (let w = 0; w < 16; w++) {
    const before = new Map([...e.bodies].map(([id, bb]) => [id, { ...bb.pos }]))
    for (let i = 0; i < 500; i++) settleStep(e)
    let worst = 0
    for (const [id, bb] of e.bodies) {
      const p = before.get(id)!
      worst = Math.max(worst, Math.hypot(bb.pos.x - p.x, bb.pos.y - p.y))
    }
    if (w % 3 === 1 || w === 15) console.log(`  ${combo.name} window ${w}: worst drift ${worst.toFixed(3)} resamples=${debugCounts.resample} E=${wireEnergy(e).toFixed(3)}`)
    debugCounts.resample = 0
  }
})
