import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('DiagramBuilder', () => {
  it('builds a valid diagram with deterministic ids', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const bub = b.bubble(cut, 1)
    const t = b.termNode(bub, p('\\x. x'))
    const a = b.atom(bub, bub)
    b.wire(bub, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    expect(cut).toBe('r1')
    expect(bub).toBe('r2')
    expect(t).toBe('n0')
    expect(a).toBe('n1')
    expect(Object.keys(d.wires)).toEqual(['w0'])
    expect(d.regions['r2']).toEqual({ kind: 'bubble', parent: 'r1', arity: 1 })
  })

  it('auto-attaches a fresh singleton wire to every unattached port, scoped at the node region', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. y (z x)')) // ports: out, v:y, v:z — none wired
    const d = b.build()
    const wires = Object.values(d.wires)
    expect(wires).toHaveLength(3)
    const keys = wires.flatMap((w) => w.endpoints.map((ep) => `${ep.node}/${portKey(ep.port)}`)).sort()
    expect(keys).toEqual([`${t}/out`, `${t}/v:y`, `${t}/v:z`])
    for (const w of wires) {
      expect(w.scope).toBe(b.root)
      expect(w.endpoints).toHaveLength(1)
    }
  })

  it('produces a diagram that passes validation even with mixed manual and auto wires', () => {
    const b = new DiagramBuilder()
    const t1 = b.termNode(b.root, p('\\x. y x'))
    const t2 = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [
      { node: t1, port: { kind: 'freeVar', name: 'y' } },
      { node: t2, port: { kind: 'output' } },
    ])
    const d = b.build() // t1/out auto-wired
    expect(Object.keys(d.wires)).toHaveLength(2)
  })

  it('build() is repeatable and rejects double-building mutations cleanly', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const d1 = b.build()
    const d2 = b.build()
    expect(Object.keys(d1.wires)).toEqual(Object.keys(d2.wires))
  })
})
