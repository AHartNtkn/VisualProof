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
    // the consumer's residual free (source 'y') is canonical s0 after construction
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(\\x. x) s0')))
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
    // the producer's first free and the consumer's residual free ride ONE wire
    // (same individual) even though their canonical names differ (producer s0,
    // consumer s1): fusion collapses them onto the consumer's existing
    // endpoint, so the merged term has TWO distinct ports, the shared one
    // occurring twice — canonically 's0 s1 s0'
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('s0 s1 s0')))
    expect(out.wires[shared]?.endpoints).toHaveLength(1)
    expect(out.wires[shared]?.endpoints[0]).toEqual({ node: b, port: { kind: 'freeVar', name: 's0' } })
  })

  it('freshens colliding ports wired differently', () => {
    // producer 'y z' canonicalizes to (s0 s1), consumer 'q y' to (s0 s1) with
    // s0 consumed; the producer's s1 and the consumer's residual s1 share a
    // NAME but ride DIFFERENT (auto-singleton) wires — two distinct
    // individuals that fusion must keep apart by freshening, not conflate
    const h2 = new DiagramBuilder()
    const a2 = h2.termNode(h2.root, p('y z'))
    const b2 = h2.termNode(h2.root, p('q y'))
    const w2 = h2.wire(h2.root, [
      { node: a2, port: { kind: 'output' } },
      { node: b2, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d2 = h2.build()
    // the producer's two singleton wires and the consumer's residual wire
    const singleton = (node: string, name: string): string => {
      const found = Object.entries(d2.wires).find(([, wv]) =>
        wv.endpoints.some((ep) => ep.node === node && ep.port.kind === 'freeVar' && ep.port.name === name))
      if (found === undefined) throw new Error(`no wire holds 'v:${name}' of '${node}'`)
      return found[0]
    }
    const waY = singleton(a2, 's0')
    const waZ = singleton(a2, 's1')
    const wb = singleton(b2, 's1')
    const out = applyFusion(d2, w2)
    const merged = out.nodes[b2]
    // three DISTINCT ports survive: (producer-y producer-z) consumer-y,
    // canonically s0 s1 s2 in first-occurrence order
    expect(merged?.kind === 'term' && termEq(merged.term, app(app(port('s0'), port('s1')), port('s2')))).toBe(true)
    // each port stays on ITS OWN original wire: migrating the freshened
    // producer port onto the consumer's wire would conflate two individuals
    expect(out.wires[waY]?.endpoints).toEqual([{ node: b2, port: { kind: 'freeVar', name: 's0' } }])
    expect(out.wires[waZ]?.endpoints).toEqual([{ node: b2, port: { kind: 'freeVar', name: 's1' } }])
    expect(out.wires[wb]?.endpoints).toEqual([{ node: b2, port: { kind: 'freeVar', name: 's2' } }])
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
    // the host's sole free (source 'y') is canonical s0; the extracted
    // producer's copy of it shares the SAME wire
    const yWire = Object.entries(split.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.port.kind === 'freeVar' && ep.port.name === 's0'))
    expect(yWire, 'expected a wire holding a v:s0 endpoint').toBeDefined()
    expect(yWire![1].endpoints).toHaveLength(2)
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
