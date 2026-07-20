import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { app, port, termEq } from '../../../src/kernel/term/term'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { applyFusion, applyFission } from '../../../src/kernel/rules/fusion'

const p = (s: string) => parseTerm(s)

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

  it('compacts occurring support and removes every unused source endpoint', () => {
    const h = new DiagramBuilder()
    const producer = h.termNode(h.root, p('usedP'), ['unusedP', 'usedP'])
    const consumer = h.termNode(h.root, p('slot kept'), ['unusedC', 'slot', 'kept'])
    const unusedProducerWire = h.wire(h.root, [
      { node: producer, port: { kind: 'freeVar', name: 'unusedP' } },
    ])
    const producerFreeWire = h.wire(h.root, [
      { node: producer, port: { kind: 'freeVar', name: 'usedP' } },
    ])
    const unusedConsumerWire = h.wire(h.root, [
      { node: consumer, port: { kind: 'freeVar', name: 'unusedC' } },
    ])
    const keptConsumerWire = h.wire(h.root, [
      { node: consumer, port: { kind: 'freeVar', name: 'kept' } },
    ])
    const fusedWire = h.wire(h.root, [
      { node: producer, port: { kind: 'output' } },
      { node: consumer, port: { kind: 'freeVar', name: 'slot' } },
    ])

    const out = applyFusion(h.build(), fusedWire)
    const merged = out.nodes[consumer]
    expect(merged?.kind).toBe('term')
    if (merged?.kind !== 'term') throw new Error('expected merged term node')
    expect(merged.freePorts).toEqual(['s0', 's1'])
    expect(printTerm(merged.term)).toBe(printTerm(p('s0 s1')))
    expect(out.wires[fusedWire]).toBeUndefined()
    expect(out.wires[unusedProducerWire]?.endpoints).toEqual([])
    expect(out.wires[unusedConsumerWire]?.endpoints).toEqual([])
    expect(out.wires[producerFreeWire]?.endpoints).toEqual([
      { node: consumer, port: { kind: 'freeVar', name: 's0' } },
    ])
    expect(out.wires[keptConsumerWire]?.endpoints).toEqual([
      { node: consumer, port: { kind: 'freeVar', name: 's1' } },
    ])
  })

  it("applies collapse renames in ONE simultaneous pass: a collapse target equal to another producer port's original name must not cascade", () => {
    // producer 'a b' → canonical (s0 s1); consumer 'q y z' → canonical
    // s0 s1 s2 with s0 consumed. Producer s0 shares a wire with consumer s1,
    // producer s1 with consumer s2, so the collapse renames are
    // {s0→s1, s1→s2}: the first rename's TARGET is the second's SOURCE.
    // Sequential substitution would funnel both producer ports into s2,
    // conflating two distinct individuals.
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('a b'))
    const b = h.termNode(h.root, p('q y z'))
    const shared1 = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'a' } },
      { node: b, port: { kind: 'freeVar', name: 'y' } },
    ])
    const shared2 = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'b' } },
      { node: b, port: { kind: 'freeVar', name: 'z' } },
    ])
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = h.build()
    const out = applyFusion(d, w)
    const merged = out.nodes[b]
    // (consumer-y consumer-z) consumer-y consumer-z — TWO individuals, each
    // used twice; canonically (s0 s1) s0 s1
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('(s0 s1) s0 s1')))
    // one endpoint per individual, each on its original wire
    expect(out.wires[shared1]?.endpoints).toEqual([{ node: b, port: { kind: 'freeVar', name: 's0' } }])
    expect(out.wires[shared2]?.endpoints).toEqual([{ node: b, port: { kind: 'freeVar', name: 's1' } }])
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
    expect(exploreForm(applyFusion(split, newWire))).toBe(exploreForm(d))
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

  it('keeps every original wire association inside a multi-free-port term (positions stable)', () => {
    // host 'a (b c)' → canonical s0 (s1 s2), each free on its own explicit
    // wire. Extracting the arg must leave s0 on the host's original wire and
    // put the producer's canonical (s0 s1) on b's and c's original wires —
    // position is the invariant, the spelling is forced by it.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('a (b c)'))
    const wA = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'a' } }])
    const wB = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'b' } }])
    const wC = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'c' } }])
    const d = h.build()
    const split = applyFission(d, n, ['arg'])
    const producer = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
    expect(split.wires[wA]?.endpoints).toEqual([{ node: n, port: { kind: 'freeVar', name: 's0' } }])
    expect(split.wires[wB]?.endpoints).toEqual([{ node: producer, port: { kind: 'freeVar', name: 's0' } }])
    expect(split.wires[wC]?.endpoints).toEqual([{ node: producer, port: { kind: 'freeVar', name: 's1' } }])
    // and fusion inverts it exactly
    const newWire = Object.keys(split.wires).find(
      (id) => d.wires[id] === undefined && split.wires[id]!.endpoints.length === 2,
    )!
    expect(exploreForm(applyFusion(split, newWire))).toBe(exploreForm(d))
  })

  it('compacts producer and residual separately, removes unused endpoints, and keeps the fresh port distinct', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('keep extracted'), ['q', 'keep', 'extracted'])
    const unusedWire = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'q' } },
    ])
    const keptWire = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'keep' } },
    ])
    const extractedWire = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'extracted' } },
    ])
    const before = h.build()

    const split = applyFission(before, n, ['arg'])
    const producer = Object.keys(split.nodes).find((id) => before.nodes[id] === undefined)
    expect(producer).toBeDefined()
    const residualNode = split.nodes[n]
    const producerNode = split.nodes[producer!]
    expect(residualNode?.kind).toBe('term')
    expect(producerNode?.kind).toBe('term')
    if (residualNode?.kind !== 'term' || producerNode?.kind !== 'term') {
      throw new Error('expected residual and producer term nodes')
    }
    expect(residualNode.freePorts).toEqual(['s0', 's1'])
    expect(producerNode.freePorts).toEqual(['s0'])
    expect(new Set(residualNode.freePorts).size).toBe(residualNode.freePorts.length)
    expect(printTerm(residualNode.term)).toBe(printTerm(p('s0 s1')))
    expect(printTerm(producerNode.term)).toBe(printTerm(p('s0')))
    expect(split.wires[unusedWire]?.endpoints).toEqual([])
    expect(split.wires[keptWire]?.endpoints).toEqual([
      { node: n, port: { kind: 'freeVar', name: 's0' } },
    ])
    expect(split.wires[extractedWire]?.endpoints).toEqual([
      { node: producer, port: { kind: 'freeVar', name: 's0' } },
    ])
    const connecting = Object.values(split.wires).find((wire) =>
      wire.endpoints.some((ep) => ep.node === producer && ep.port.kind === 'output'))
    expect(connecting?.endpoints).toContainEqual({ node: n, port: { kind: 'freeVar', name: 's1' } })
  })

  it('round-trips a shared free spelled DIFFERENTLY on the two nodes: fusion yields ONE port on the shared wire, used in both positions', () => {
    // host 'y ((\x. x) z y)' → canonical 's0 ((\x. x) s1 s0)'. Extracting the
    // arg yields a producer '(\x. x) s0 s1' whose s1 rides the host's s0
    // wire: ONE individual, spelled s1 on the producer and s0 on the host.
    // The inverse fusion must collapse the pair to a single endpoint on that
    // wire, and the merged term must use that variable in BOTH positions.
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y ((\\x. x) z y)'))
    const d = h.build()
    const split = applyFission(d, n, ['arg'])
    const producer = Object.keys(split.nodes).find((id) => d.nodes[id] === undefined)!
    const sharedEntry = Object.entries(split.wires).find(([, w]) =>
      w.endpoints.length === 2 && w.endpoints.every((ep) => ep.port.kind === 'freeVar'))
    expect(sharedEntry, 'expected the shared individual to ride one two-endpoint freeVar wire').toBeDefined()
    const [shared, sharedW] = sharedEntry!
    expect(sharedW.endpoints).toContainEqual({ node: n, port: { kind: 'freeVar', name: 's0' } })
    expect(sharedW.endpoints).toContainEqual({ node: producer, port: { kind: 'freeVar', name: 's1' } })
    const newWire = Object.entries(split.wires).find(([, w]) =>
      w.endpoints.some((ep) => ep.node === producer && ep.port.kind === 'output'))![0]
    const out = applyFusion(split, newWire)
    const merged = out.nodes[n]
    // the shared individual is ONE variable (s0), used in the head position
    // AND inside the inlined producer
    expect(merged?.kind === 'term' && printTerm(merged.term)).toBe(printTerm(p('s0 ((\\x. x) s1 s0)')))
    expect(out.wires[shared]?.endpoints).toEqual([{ node: n, port: { kind: 'freeVar', name: 's0' } }])
    expect(exploreForm(out)).toBe(exploreForm(d))
  })

  it('compacts different local ports on one global wire before extracting the producer', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('keep (left right)'))
    h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'keep' } }])
    const shared = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'left' } },
      { node: n, port: { kind: 'freeVar', name: 'right' } },
    ])
    const before = h.build()

    const split = applyFission(before, n, ['arg'])
    const producer = Object.keys(split.nodes).find((id) => before.nodes[id] === undefined)!
    const producerNode = split.nodes[producer]
    expect(producerNode?.kind === 'term' && producerNode.freePorts).toEqual(['s0'])
    expect(producerNode?.kind === 'term' && printTerm(producerNode.term)).toBe(printTerm(p('s0 s0')))
    expect(split.wires[shared]?.endpoints).toEqual([
      { node: producer, port: { kind: 'freeVar', name: 's0' } },
    ])

    const bridge = Object.entries(split.wires).find(([, wire]) =>
      wire.endpoints.some((ep) => ep.node === producer && ep.port.kind === 'output'))![0]
    const fused = applyFusion(split, bridge)
    const fusedNode = fused.nodes[n]
    expect(fusedNode?.kind === 'term' && printTerm(fusedNode.term)).toBe(printTerm(p('s0 (s1 s1)')))
    expect(fused.wires[shared]?.endpoints).toEqual([
      { node: n, port: { kind: 'freeVar', name: 's1' } },
    ])
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
