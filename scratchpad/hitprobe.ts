// OBSERVATION: geometry at the failing hittest click — which wires' curves are near it?
import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { parseTerm } from '../src/kernel/term/parse'
import { mkEngine } from '../src/view/engine'
import { settle, recomputeRegions } from '../src/view/relax'
import { legPaths } from '../src/view/wires'

const p = (s: string) => parseTerm(s)
const h = new DiagramBuilder()
const a = h.termNode(h.root, p('x'))
const b = h.termNode(h.root, p('x'))
const c = h.termNode(h.root, p('x'))
const w = h.wire(h.root, [
  { node: a, port: { kind: 'freeVar', name: 'x' } },
  { node: b, port: { kind: 'freeVar', name: 'x' } },
  { node: c, port: { kind: 'freeVar', name: 'x' } },
])
const e = mkEngine(h.build(), [])
const used = settle(e, 2600)
recomputeRegions(e)
console.log(`settle used ${used}`)
const legs = legPaths(e).filter((l) => l.wid === w)
const curve = legs.map((l) => l.pts).find((pl) => pl.length > 2)!
const mid = curve[Math.floor(curve.length / 2)]!
console.log('click point:', mid)
const distTo = (pts: { x: number; y: number }[]): number =>
  Math.min(...pts.map((q) => Math.hypot(q.x - mid.x, q.y - mid.y)))
for (const l of legPaths(e)) console.log(`wire ${l.wid}: minDist=${distTo(l.pts).toFixed(3)} pts=${l.pts.length}`)
for (const [id, body] of e.bodies) console.log(`body ${id} kind=${body.kind} at (${body.pos.x.toFixed(1)},${body.pos.y.toFixed(1)})`)

// Is this a TRUE rest? Full-E finite-difference gradient over body coords at the rest.
import { totalEnergy } from '../src/view/relax'
const E0 = totalEnergy(e)
let gn2 = 0
const gs: [string, number, number][] = []
for (const [id, body] of e.bodies) {
  const probe = (ax: 'x' | 'y'): number => {
    const s = body.pos[ax]
    body.pos = { ...body.pos, [ax]: s + 0.01 }; const ep = totalEnergy(e)
    body.pos = { ...body.pos, [ax]: s - 0.01 }; const em = totalEnergy(e)
    body.pos = { ...body.pos, [ax]: s }
    return (ep - em) / 0.02
  }
  const gx = probe('x'), gy = probe('y')
  gn2 += gx * gx + gy * gy
  gs.push([id, gx, gy])
}
console.log(`E0=${E0.toFixed(3)} fullGradNorm(bodies)=${Math.sqrt(gn2).toFixed(4)}`)
for (const [id, gx, gy] of gs) console.log(`  ∂E/∂${id} = (${gx.toFixed(3)}, ${gy.toFixed(3)})`)
