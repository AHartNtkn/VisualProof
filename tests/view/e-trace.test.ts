import { it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep, wireEnergy, debugNetWire } from '../../src/view/relax'
import { debugCounts } from '../../src/view/wirechain'

it('TRACE which fixture misbehaves', () => {
  const mks: Record<string, () => { d: ReturnType<DiagramBuilder['build']>; b: string[] }> = {
    interposed: () => {
      const b = new DiagramBuilder()
      const r1 = b.ref(b.root, 'a', 1), r2 = b.ref(b.root, 'b', 1)
      b.ref(b.root, 'wall', 1)
      b.termNode(b.root, parseTerm('\\x. x'))
      b.wire(b.root, [
        { node: r1, port: { kind: 'arg', index: 0 } },
        { node: r2, port: { kind: 'arg', index: 0 } },
      ])
      return { d: b.build(), b: [] }
    },
    plain2: () => {
      const b = new DiagramBuilder()
      const r1 = b.ref(b.root, 'lt', 2), r2 = b.ref(b.root, 'gt', 2)
      b.wire(b.root, [
        { node: r1, port: { kind: 'arg', index: 0 } },
        { node: r2, port: { kind: 'arg', index: 0 } },
      ])
      return { d: b.build(), b: [] }
    },
    inCutOnly: () => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const r1 = b.ref(cut, 'lt', 2), r2 = b.ref(cut, 'gt', 2)
      b.wire(cut, [
        { node: r1, port: { kind: 'arg', index: 0 } },
        { node: r2, port: { kind: 'arg', index: 0 } },
      ])
      return { d: b.build(), b: [] }
    },
    forallShape: () => {
      const b = new DiagramBuilder()
      const cut = b.cut(b.root)
      const r1 = b.ref(cut, 'lt', 2), r2 = b.ref(cut, 'gt', 2)
      b.wire(b.root, [
        { node: r1, port: { kind: 'arg', index: 0 } },
        { node: r2, port: { kind: 'arg', index: 0 } },
      ])
      return { d: b.build(), b: [] }
    },
  }
  for (const [name, mk] of Object.entries(mks)) {
    const { d, b } = mk()
    const e = mkEngine(d, b as never[])
    settle(e, 2600)
    const before = new Map([...e.bodies].map(([id, bb]) => [id, { ...bb.pos }]))
    let prev = wireEnergy(e)
    let rises = 0, maxRise = 0
    for (let i = 0; i < 200; i++) {
      settleStep(e)
      const cur = wireEnergy(e)
      const ev = `${debugCounts.resample}/${debugCounts.resampleReverted}/${debugCounts.topoSplit}/${debugCounts.topoMerge}`
      debugCounts.resample = 0; debugCounts.resampleReverted = 0; debugCounts.topoSplit = 0; debugCounts.topoMerge = 0
      if (cur > prev + 0.5) console.log(`  ${name} t${i}: +${(cur - prev).toFixed(3)} ev=${ev}`)
      if (cur > prev + 1e-6) { rises++; maxRise = Math.max(maxRise, cur - prev) }
      prev = cur
    }
    let netAvg = { x: 0, y: 0 }
    for (let i = 0; i < 20; i++) {
      settleStep(e)
      netAvg.x += debugNetWire.x / 20
      netAvg.y += debugNetWire.y / 20
    }
    console.log(`  ${name} avg net wire force: (${netAvg.x.toFixed(3)}, ${netAvg.y.toFixed(3)})`)
    const drift = [...e.bodies].map(([id, bb]) => {
      const p = before.get(id)!
      return { id, d: Math.hypot(bb.pos.x - p.x, bb.pos.y - p.y) }
    }).sort((a, b2) => b2.d - a.d).slice(0, 4)
    console.log(`${name}: E=${prev.toFixed(2)} rises=${rises} maxRise=${maxRise.toFixed(4)} drift: ${drift.map((x) => `${x.id}=${x.d.toFixed(3)}`).join(' ')}`)
  }
})
