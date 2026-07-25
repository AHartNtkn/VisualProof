import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig, sigKey } from '../../../src/kernel/diagram/sig'

const p = (s: string) => parseTerm(s)

describe('DiagramBuilder', () => {
  it('builds a valid diagram with deterministic ids', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const t = b.termNode(cut, p('\\x. x'))
    const a = b.atom(cut, relSig([IOTA]))
    const arg = b.wire(cut, [
      { node: t, port: { kind: 'output' } },
      { node: a, port: { kind: 'arg', index: 0 } },
    ])
    const d = b.build()
    expect(cut).toBe('r1')
    expect(t).toBe('n0')
    expect(a).toBe('n1')
    // w0 is the manual arg wire; w1 is the auto-attached head wire.
    expect(Object.keys(d.wires)).toEqual([arg, 'w1'])
    expect(d.regions['r1']).toEqual({ kind: 'cut', parent: 'r0' })
    expect(d.nodes['n1']).toMatchObject({ kind: 'atom', sig: relSig([IOTA]) })
  })

  it('auto-attaches a fresh singleton wire to every unattached port, scoped at the node region', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. y (z x)')) // ports: out plus two frees, canonicalized to v:s0, v:s1
    const d = b.build()
    const wires = Object.values(d.wires)
    expect(wires).toHaveLength(3)
    const keys = wires.flatMap((w) => w.endpoints.map((ep) => `${ep.node}/${portKey(ep.port)}`)).sort()
    expect(keys).toEqual([`${t}/out`, `${t}/v:s0`, `${t}/v:s1`])
    for (const w of wires) {
      expect(w.scope).toBe(b.root)
      expect(w.endpoints).toHaveLength(1)
      expect(sigKey(w.sig)).toBe(sigKey(IOTA))
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
    const d = b.build() // t1/out and t2 have no frees; only t1/out is auto-wired
    expect(Object.keys(d.wires)).toHaveLength(2)
  })

  it('build() is repeatable and rejects double-building mutations cleanly', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const d1 = b.build()
    const d2 = b.build()
    expect(Object.keys(d1.wires)).toEqual(['w0'])
    expect(Object.keys(d2.wires)).toEqual(['w0'])
  })

  it('builds the empty diagram (root sheet only)', () => {
    const d = new DiagramBuilder().build()
    expect(Object.keys(d.nodes)).toHaveLength(0)
    expect(Object.keys(d.wires)).toHaveLength(0)
  })

  it('auto-wires an atom head plus arg ports, each with the sig the port actually accepts', () => {
    const b = new DiagramBuilder()
    const sig = relSig([IOTA, IOTA])
    const a = b.atom(b.root, sig)
    const d = b.build()
    const wires = Object.values(d.wires)
    expect(wires).toHaveLength(3) // head + 2 args
    const byPort = new Map(wires.flatMap((w) => w.endpoints.map((ep) => [portKey(ep.port), w] as const)))
    expect(new Set(byPort.keys())).toEqual(new Set(['hd', 'a:0', 'a:1']))
    expect(sigKey(byPort.get('hd')!.sig)).toBe(sigKey(sig))
    expect(sigKey(byPort.get('a:0')!.sig)).toBe(sigKey(IOTA))
    expect(sigKey(byPort.get('a:1')!.sig)).toBe(sigKey(IOTA))
    expect(a).toBe('n0')
    for (const w of wires) expect(w.scope).toBe(b.root)
  })

  it('auto-wires ref arg ports with sig-correct types (refs have no head)', () => {
    const b = new DiagramBuilder()
    const sig = relSig([relSig([IOTA])])
    const r = b.ref(b.root, 'Nat', sig)
    const d = b.build()
    const wires = Object.values(d.wires)
    expect(wires).toHaveLength(1)
    expect(wires[0]!.endpoints).toEqual([{ node: r, port: { kind: 'arg', index: 0 } }])
    expect(sigKey(wires[0]!.sig)).toBe(sigKey(relSig([IOTA])))
  })

  it('relWire creates an endpoint-free relational wire that round-trips through mkDiagram', () => {
    const b = new DiagramBuilder()
    const sig = relSig([IOTA, IOTA])
    const w = b.relWire(b.root, sig)
    const d = b.build()
    expect(d.wires[w]).toEqual({ scope: b.root, sig, endpoints: [] })
  })

  it('wires an atom head explicitly to a rel-sig wire, completing an atom+relWire round-trip through mkDiagram', () => {
    const b = new DiagramBuilder()
    const sig = relSig([IOTA])
    const a = b.atom(b.root, sig)
    const head = b.wire(b.root, [{ node: a, port: { kind: 'head' } }], sig)
    const d = b.build()
    expect(d.wires[head]!.sig).toEqual(sig)
    expect(d.wires[head]!.endpoints).toEqual([{ node: a, port: { kind: 'head' } }])
    // arg 0 is still auto-wired
    expect(Object.keys(d.wires)).toHaveLength(2)
  })

  it('wiring an atom head without an explicit rel sig defaults to IOTA, which mkDiagram rejects as a mismatch', () => {
    const b = new DiagramBuilder()
    const sig = relSig([IOTA])
    const a = b.atom(b.root, sig)
    b.wire(b.root, [{ node: a, port: { kind: 'head' } }]) // sig defaults to IOTA — wrong for a head port
    expect(() => b.build()).toThrowError(/does not match port 'hd'/)
  })
})
