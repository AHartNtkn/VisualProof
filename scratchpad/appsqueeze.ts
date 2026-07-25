// App-faithful squeeze: app frame/scale, 4-terminal wire, GRADUAL pinned drag.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, recomputeRegions, totalEnergy } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
e.frame = { center: { x: 6, y: 0 }, half: 11 }
e.scale = 0.33
const wire = e.wires.get(w)!
const put = (i: number, x: number, y: number) => { const bd = e.bodies.get(rs[i]!)!; bd.pos = { x, y }; bd.theta = 0 }
;[[-2, -3], [-2, 3], [14, -3], [14, 3]].forEach(([x, y], i) => put(i, x!, y!))
recomputeRegions(e)
const pinned = new Set(rs)
for (let t = 0; t < 900; t++) if (!settleStep(e, pinned)) break
const pairing = () => {
  const g = (bi: number) => wire.legs
    .filter((l) => (l.a.kind === 'branch' && l.a.i === bi) || (l.b.kind === 'branch' && l.b.i === bi))
    .flatMap((l) => (l.a.kind === 'bind' ? [l.a.i] : l.b.kind === 'bind' ? [l.b.i] : [])).sort().join('')
  return `{${g(0)}}|{${g(1)}}`
}
const sep = () => wire.branches.length === 2 ? Math.hypot(wire.branches[1]!.x - wire.branches[0]!.x, wire.branches[1]!.y - wire.branches[0]!.y).toFixed(3) : 'n/a'
console.log(`wide rest: pairing=${pairing()} branchSep=${sep()} E=${totalEnergy(e).toFixed(1)}`)
// GRADUAL squeeze: drag the two right terminals leftward 0.15/frame (app-like),
// physics interleaved every frame, ending nearly on top of the left pair
for (let step = 0; step < 100; step++) {
  const t = (step + 1) / 100
  put(2, 14 - 15.2 * t, -3)
  put(3, 14 - 15.2 * t, 3)
  settleStep(e, pinned)
}
console.log(`mid-drag: pairing=${pairing()} branchSep=${sep()}`)
for (let t = 0; t < 900; t++) if (!settleStep(e, pinned)) break
console.log(`squeezed rest: pairing=${pairing()} branchSep=${sep()} E=${totalEnergy(e).toFixed(1)}`)
// now pull apart VERTICALLY (should re-pair to rows)
for (let step = 0; step < 100; step++) {
  const t = (step + 1) / 100
  put(0, -2, -3 - 12 * t); put(1, -2, 3 + 12 * t)
  put(2, -1.2, -3 - 12 * t); put(3, -1.2, 3 + 12 * t)
  settleStep(e, pinned)
}
;(globalThis as { __ct?: boolean }).__ct = true
settleStep(e, pinned)
;(globalThis as { __ct?: boolean }).__ct = false
for (let t = 0; t < 900; t++) if (!settleStep(e, pinned)) break
console.log(`pulled-tall rest: pairing=${pairing()} branchSep=${sep()} E=${totalEnergy(e).toFixed(1)}`)

// decompose dE/dl at the squeezed trap: which term holds the edge open?
import { wireEnergy, contentEnergy } from '../src/view/relax'
const m = { x: (wire.branches[0]!.x + wire.branches[1]!.x) / 2, y: (wire.branches[0]!.y + wire.branches[1]!.y) / 2 }
const dir = (() => { const dx = wire.branches[1]!.x - wire.branches[0]!.x, dy = wire.branches[1]!.y - wire.branches[0]!.y; const dd = Math.hypot(dx, dy); return { x: dx / dd, y: dy / dd } })()
const setSep = (s: number) => {
  wire.branches[0] = { x: m.x - dir.x * s / 2, y: m.y - dir.y * s / 2 }
  wire.branches[1] = { x: m.x + dir.x * s / 2, y: m.y + dir.y * s / 2 }
  recomputeRegions(e)
}
console.log('sep sweep (current chart): sep → wireE | contentE')
for (const s of [15, 10, 7, 5, 3, 1.5, 0.5, 0.1, 0.02]) {
  setSep(s)
  console.log(`  ${s}: ${wireEnergy(e).toFixed(1)} | ${contentEnergy(e).toFixed(1)}`)
}
