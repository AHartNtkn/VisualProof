// Probe 1: precise via detection by END-body id prefix (x: = ∀ via, j: = ∃ tip).
import { bootFixture } from '../tests/app/boot-fixture'
import { mkReplay } from '../src/app/replay'
import { mkEngine } from '../src/view/engine'

const boot = (await bootFixture()).ctx
console.log('theorems in boot:', [...boot.theorems.keys()].join(', '))

for (const name of [...boot.theorems.keys()]) {
  const r = mkReplay(name, boot)
  let maxVia = 0, maxTip = 0, maxBr = 0, viaSteps: number[] = []
  for (let k = 0; k <= r.actionCount; k++) {
    const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
    let via = 0, tip = 0, br = 0
    for (const w of e.wires.values()) {
      if (w.endBodyId?.startsWith('x:')) via++
      if (w.endBodyId?.startsWith('j:')) tip++
      br += w.branches.length
    }
    if (via > 0) viaSteps.push(k)
    maxVia = Math.max(maxVia, via); maxTip = Math.max(maxTip, tip); maxBr = Math.max(maxBr, br)
  }
  console.log(`${name}: maxVia=${maxVia} maxTip=${maxTip} maxBr=${maxBr} viaSteps=[${viaSteps.slice(0,8).join(',')}${viaSteps.length>8?'…':''}]`)
}
