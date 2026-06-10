import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { app, port, termEq } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { applyFusion, applyFission } from '../../../src/kernel/rules/fusion'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('applyFusion', () => {
  it('inlines a producer along a two-endpoint wire (one-point rule)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const b = h.termNode(h.root, p('q y'))
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = h.build()
    const out = applyFusion(d, w)
    expect(out.nodes[a]).toBeUndefined()
    expect(out.wires[w]).toBeUndefined()
    const merged = out.nodes[b]
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(\\x. x) y')))
  })

  it('migrates the producer ports onto the consumer, sharing wires where they already share', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('y z'))
    const b = h.termNode(h.root, p('q y'))
    const shared = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'y' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = h.build()
    const out = applyFusion(d, w)
    const merged = out.nodes[b]
    // y shared the same wire: no rename, single y port carried by b's old endpoint
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(y z) y')))
    expect(out.wires[shared]?.endpoints).toHaveLength(1)
    expect(out.wires[shared]?.endpoints[0]?.node).toBe(b)
  })

  it('freshens colliding ports wired differently', () => {
    // builder auto-singleton wires: a.y and b.y are DIFFERENT wires, so the
    // producer's y must be freshened to y_0 (compare via constructors — the
    // parser need not accept underscores in identifiers)
    const h2 = new DiagramBuilder()
    const a2 = h2.termNode(h2.root, p('y'))
    const b2 = h2.termNode(h2.root, p('q y'))
    const w2 = h2.wire(h2.root, [
      { node: a2, port: { kind: 'output' } },
      { node: b2, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d2 = h2.build()
    // the producer's and consumer's distinct y wires (auto-singleton)
    const wa = Object.entries(d2.wires).find(([, wv]) =>
      wv.endpoints.some((ep) => ep.node === a2 && ep.port.kind === 'freeVar' && ep.port.name === 'y'))![0]
    const wb = Object.entries(d2.wires).find(([, wv]) =>
      wv.endpoints.some((ep) => ep.node === b2 && ep.port.kind === 'freeVar' && ep.port.name === 'y'))![0]
    const out = applyFusion(d2, w2)
    const merged = out.nodes[b2]
    expect(merged?.kind === 'term' && termEq(merged.term, app(port('y_0'), port('y')))).toBe(true)
    // the freshened port must stay on the PRODUCER's wire: migrating it to the
    // consumer's wire would conflate two distinct individuals under one wire
    expect(out.wires[wa]?.endpoints).toEqual([{ node: b2, port: { kind: 'freeVar', name: 'y_0' } }])
    expect(out.wires[wb]?.endpoints).toEqual([{ node: b2, port: { kind: 'freeVar', name: 'y' } }])
  })

  it('rejects wires of the wrong shape, self-loops, and displaced producers, by name', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const b = h.termNode(h.root, p('\\x. \\y. x'))
    const w3 = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'output' } },
    ])
    const d = h.build()
    expect(() => applyFusion(d, w3)).toThrowError(/one output endpoint and one freeVar endpoint/)

    const h2 = new DiagramBuilder()
    const n = h2.termNode(h2.root, p('q'))
    const loop = h2.wire(h2.root, [
      { node: n, port: { kind: 'output' } },
      { node: n, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d2 = h2.build()
    expect(() => applyFusion(d2, loop)).toThrowError(/cannot inline a node into itself/)

    const h3 = new DiagramBuilder()
    const cut = h3.cut(h3.root)
    const a3 = h3.termNode(cut, p('\\x. x'))
    const b3 = h3.termNode(cut, p('q'))
    const w4 = h3.wire(h3.root, [
      { node: a3, port: { kind: 'output' } },
      { node: b3, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d3 = h3.build()
    expect(() => applyFusion(d3, w4)).toThrowError(/producing node to sit at the wire's scope/)
  })
})

describe('applyFission', () => {
  it('extracts a bvar-closed subterm to a new node; fusion inverts it (fingerprint)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n = h.termNode(cut, p('(\\x. x) y'))
    const d = h.build()
    const split = applyFission(d, n, ['fn'])
    const producer = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
    expect(split.nodes[producer]?.kind).toBe('term')
    const newWire = Object.keys(split.wires).find(
      (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
    )!
    expect(split.wires[newWire]?.scope).toBe(cut)
    expect(diagramFingerprint(applyFusion(split, newWire))).toBe(diagramFingerprint(d))
  })

  it('keeps shared ports attached on both nodes', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y ((\\x. x) y)'))
    const d = h.build()
    const split = applyFission(d, n, ['arg'])
    const yWire = Object.entries(split.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.port.kind === 'freeVar' && ep.port.name === 'y'))![1]
    expect(yWire.endpoints).toHaveLength(2)
  })

  it('rejects subterms that reference outer binders, by name', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x y'))
    const d = h.build()
    expect(() => applyFission(d, n, ['body']))
      .toThrowError(/bvar-closed subterm/)
  })

  it('rejects invalid paths as malformed input', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const d = h.build()
    expect(() => applyFission(d, n, ['fn'])).toThrowError(/invalid path/)
  })
})
