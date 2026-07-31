import { DiagramBuilder } from '../src/kernel/diagram/builder'
import { relSig, TERM } from '../src/kernel/diagram/sig'
import { mkEngine, type WireLeg, type WireLegEnd } from '../src/view/engine'
import { mkLegCache } from '../src/view/elastica'
import { settleStep, seedProject, totalEnergy } from '../src/view/relax'
const rel1 = relSig([TERM])
const b = new DiagramBuilder()
const rs = Array.from({ length: 4 }, (_, i) => b.ref(b.root, `n${i}`, rel1))
const w = b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
const e = mkEngine(b.build(), [])
rs.forEach((id, i) => { const bd = e.bodies.get(id)!; bd.pos = { x: [-24, -24, 24, 24][i]!, y: [-6, 6, -6, 6][i]! }; bd.theta = 0 })
seedProject(e)
const wire = e.wires.get(w)!
const pinned = new Set(rs)
for (let t = 0; t < 3000; t++) if (!settleStep(e, pinned)) break
const E0 = totalEnergy(e)
console.log(`rest E=${E0.toFixed(3)} branches=${wire.branches.map((p) => `(${p.x.toFixed(2)},${p.y.toFixed(2)})`).join(' ')}`)
console.log('legs:', wire.legs.map((l) => `${JSON.stringify(l.a)}→${JSON.stringify(l.b)}`).join('  '))
// hand-build pairings at expansion v: branch0 gets group A, branch1 group B
const bind = (i: number): WireLegEnd => ({ kind: 'bind', i })
const br = (i: number): WireLegEnd => ({ kind: 'branch', i })
const mk = (a: WireLegEnd, bb: WireLegEnd, ang: number): WireLeg => ({ a, b: bb, angA: ang, angB: ang, cache: mkLegCache() })
const saved = { legs: [...wire.legs], b: wire.branches.map((p) => ({ ...p })) }
const m = { x: (saved.b[0]!.x + saved.b[1]!.x) / 2, y: (saved.b[0]!.y + saved.b[1]!.y) / 2 }
const test = (name: string, gA: [number, number], gB: [number, number], dir: { x: number; y: number }, v: number): void => {
  wire.branches[0] = { x: m.x - dir.x * v / 2, y: m.y - dir.y * v / 2 }
  wire.branches[1] = { x: m.x + dir.x * v / 2, y: m.y + dir.y * v / 2 }
  const c = (i: number): { x: number; y: number } => e.bodies.get(rs[i]!)!.pos
  const chord = (f: { x: number; y: number }, t: { x: number; y: number }) => Math.atan2(t.y - f.y, t.x - f.x)
  wire.legs.length = 0
  for (const [g, bi] of [[gA, 0], [gB, 1]] as const)
    for (const ti of g) wire.legs.push(mk(bind(ti), br(bi), chord(c(ti), wire.branches[bi]!)))
  wire.legs.push(mk(br(0), br(1), chord(wire.branches[0]!, wire.branches[1]!)))
  console.log(`${name} v=${v}: E=${totalEnergy(e).toFixed(3)} (dE=${(totalEnergy(e) - E0).toFixed(3)})`)
  wire.legs.length = 0; for (const l of saved.legs) wire.legs.push(l)
  wire.branches.length = 0; for (const p of saved.b) wire.branches.push({ ...p })
}
for (const v of [0.02, 0.5, 2, 8]) test('columns {01}|{23} horiz', [0, 1], [2, 3], { x: 1, y: 0 }, v)
for (const v of [0.02, 0.5, 2]) test('rows    {02}|{13} vert ', [0, 2], [1, 3], { x: 0, y: 1 }, v)
