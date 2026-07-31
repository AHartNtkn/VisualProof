// REPRO: the user's squeeze bug — a 4-terminal wire whose terminals are pinned
// into the ORTHOGONAL pairing's geometry must re-pair through the ℓ=0 face.
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
// establish the frame around the WIDE configuration (the frame is fixed for the
// diagram's lifetime; every placement below stays inside it)
{
  const ids = rs
  ids.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: [-24, -24, 24, 24][i]!, y: [-6, 6, -6, 6][i]! }; bd.theta = 0 })
}
seedProject(e)
const wire = e.wires.get(w)!
// which terminal pairs share a branch: the pairing signature
const pairing = (): string => wire.legs
  .filter((l) => l.a.kind === 'bind' || l.b.kind === 'bind')
  .map((l) => `${l.a.kind === 'bind' ? l.a.i : ''}${l.b.kind === 'bind' ? l.b.i : ''}@${l.a.kind === 'branch' ? l.a.i : (l.b as { i: number }).i}`)
  .sort().join(' ')
const place = (coords: [number, number][]): void => {
  rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: coords[i]![0], y: coords[i]![1] }; bd.theta = 0 })
}
const pinned = new Set(rs)
// Phase 1: wide rectangle (horizontal pairing is optimal)
place([[-24, -6], [-24, 6], [24, -6], [24, 6]])
for (let t = 0; t < 3000; t++) if (!settleStep(e, pinned)) break
console.log('wide rest pairing:  ', pairing(), 'branches:', wire.branches.map((p) => `(${p.x.toFixed(1)},${p.y.toFixed(1)})`).join(' '))
// Phase 2: squeeze into a tall rectangle RELABELED so the optimal grouping is
// {0,2}|{1,3} — a genuine NNI flip from phase 1's {0,1}|{2,3}
place([[-6, -24], [-6, 24], [6, -24], [6, 24]])
for (let t = 0; t < 3000; t++) if (!settleStep(e, pinned)) break
console.log('tall rest pairing:  ', pairing(), 'branches:', wire.branches.map((p) => `(${p.x.toFixed(1)},${p.y.toFixed(1)})`).join(' '))
const legsOfBranch = (bi: number): number[] => wire.legs
  .filter((l) => (l.a.kind === 'branch' && l.a.i === bi) || (l.b.kind === 'branch' && l.b.i === bi))
  .flatMap((l) => (l.a.kind === 'bind' ? [l.a.i] : l.b.kind === 'bind' ? [l.b.i] : []))
const g0 = legsOfBranch(0).sort().join(''), g1 = legsOfBranch(1).sort().join('')
// relabeled tall rectangle: 0,2 at bottom, 1,3 at top — optimal groups {0,2}|{1,3}
const ok = (g0 === '02' && g1 === '13') || (g0 === '13' && g1 === '02')
console.log(ok ? 'REPAIRED — crossing works' : `STUCK — pairing {${g0}}|{${g1}} (expected {02}|{13}): the face was not passed`)
