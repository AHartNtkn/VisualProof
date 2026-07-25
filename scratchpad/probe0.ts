// Probe 0: terrain map — frege theorem sizes, wire composition, ∀-via detection.
import { bootFixture } from '../tests/app/boot-fixture'
import { mkReplay } from '../src/app/replay'
import { mkEngine } from '../src/view/engine'
import type { Engine, WireView } from '../src/view/engine'

const boot = (await bootFixture()).ctx

// classify a wire
function wireKind(w: WireView): string {
  if (w.endBodyId !== null && w.binds.length === 1) return '∃-tip'
  if (w.endBodyId !== null && w.binds.length >= 2) return '∀-via'
  if (w.slots.length > 0) return 'boundary'
  return 'plain'
}

for (const name of [...boot.theorems.keys()]) {
  const r = mkReplay(name, boot)
  const parts: string[] = []
  for (let k = 0; k <= r.actionCount; k++) {
    const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
    let vias = 0, branches = 0, wires = 0
    for (const w of e.wires.values()) {
      wires++
      if (wireKind(w) === '∀-via') vias++
      branches += w.branches.length
    }
    parts.push(`k${k}:w${wires}/via${vias}/br${branches}`)
  }
  console.log(`THM ${name}: actionCount=${r.actionCount}`)
  console.log('   ' + parts.join(' '))
}
