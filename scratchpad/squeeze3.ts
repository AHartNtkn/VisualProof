import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine } from '../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
seedProject(e)
const wire = e.wires.get(w)!
rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: [-40, -40, 40, 40][i]!, y: [-10, 10, -10, 10][i]! }; bd.theta = 0 })
const pinned = new Set(rs)
for (let t = 0; t < 160; t++) {
  const f0 = performance.now()
  const moved = settleStep(e, pinned)
  const ms = performance.now() - f0
  if (t % 10 === 0) {
    const b0 = wire.branches[0]!, b1 = wire.branches[1]!
    const l = Math.hypot(b1.x - b0.x, b1.y - b0.y)
    console.log(`t=${t} ${ms.toFixed(0)}ms moved=${moved} E=${totalEnergy(e).toFixed(0)} b0=(${b0.x.toFixed(1)},${b0.y.toFixed(1)}) b1=(${b1.x.toFixed(1)},${b1.y.toFixed(1)}) l=${l.toFixed(2)}`)
  }
  if (!moved) { console.log(`REST at t=${t}`); break }
}

import { wireEnergy, contentEnergy } from '../src/view/relax'
import { resolveLeg } from '../src/view/engine'
import { thetaRange } from '../src/view/elastica'
console.log(`wireE=${wireEnergy(e).toFixed(0)} contentE=${contentEnergy(e).toFixed(0)}`)
for (const leg of wire.legs) {
  const sh = resolveLeg(e, wire, leg)
  console.log(`leg ${JSON.stringify(leg.a)}→${JSON.stringify(leg.b)}: L=${sh.sol.L.toFixed(1)} range=${thetaRange(sh.sol.c1, sh.sol.c2).toFixed(2)} chord=${Math.hypot(sh.p1.x - sh.p0.x, sh.p1.y - sh.p0.y).toFixed(1)} th0=${sh.th0.toFixed(2)}`)
}
for (const id of rs) { const bd = e.bodies.get(id)!; console.log(`${id}: theta=${bd.theta.toFixed(2)} pos=(${bd.pos.x},${bd.pos.y})`) }

// Does any single coordinate still descend the TRUE energy at this "rest"?
const tE = () => totalEnergy(e)
const E0 = tE()
const b0 = wire.branches
const tryMove = (label: string, f: (d: number) => void, undo: () => void): void => {
  for (const d of [0.02, -0.02, 0.2, -0.2, 1, -1]) {
    f(d); const dE = tE() - E0; undo()
    if (dE < -1e-6) { console.log(`${label} d=${d}: dE=${dE.toFixed(4)} DESCENDS`); return }
  }
  console.log(`${label}: no single-coordinate descent found`)
}
const saved0 = { ...b0[0]! }, saved1 = { ...b0[1]! }
tryMove('branch0.x', (d) => { b0[0] = { x: saved0.x + d, y: saved0.y } }, () => { b0[0] = { ...saved0 } })
tryMove('branch0.y', (d) => { b0[0] = { x: saved0.x, y: saved0.y + d } }, () => { b0[0] = { ...saved0 } })
tryMove('branch1.x', (d) => { b0[1] = { x: saved1.x + d, y: saved1.y } }, () => { b0[1] = { ...saved1 } })
tryMove('bothBranches.x', (d) => { b0[0] = { x: saved0.x + d, y: saved0.y }; b0[1] = { x: saved1.x + d, y: saved1.y } }, () => { b0[0] = { ...saved0 }; b0[1] = { ...saved1 } })
for (const [li, leg] of wire.legs.entries()) {
  if (leg.b.kind !== 'branch') continue
  const a0 = leg.angB
  tryMove(`leg${li}.angB`, (d) => { (leg as { angB: number }).angB = a0 + d }, () => { (leg as { angB: number }).angB = a0 })
}
