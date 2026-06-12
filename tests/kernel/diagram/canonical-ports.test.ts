import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import type { Term } from '../../../src/kernel/term/term'
import { freePorts, termEq } from '../../../src/kernel/term/term'
import type { Diagram, NodeId } from '../../../src/kernel/diagram/diagram'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { diagramFingerprint } from '../../../src/kernel/diagram/canonical/fingerprint'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import type { ConversionCertificate } from '../../../src/kernel/term/certificate'
import { applyCongruenceJoin } from '../../../src/kernel/rules/congruence'
import { applyDeiteration } from '../../../src/kernel/rules/iteration'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const pS = (s: string) => parseTerm(s, new Set(['SUCC']))
const empty: ConversionCertificate = { leftSteps: [], rightSteps: [] }

function termOf(d: Diagram, id: NodeId): Term {
  const n = d.nodes[id]
  if (n === undefined || n.kind !== 'term') throw new Error(`test setup: node '${id}' must be a term node`)
  return n.term
}

/** All freeVar endpoint names of one node across the whole diagram. */
function freeVarEndpointNames(d: Diagram, id: NodeId): string[] {
  const names: string[] = []
  for (const w of Object.values(d.wires)) {
    for (const ep of w.endpoints) {
      if (ep.node === id && ep.port.kind === 'freeVar') names.push(ep.port.name)
    }
  }
  return names.sort()
}

describe('name-blind free ports (canonicalization at construction)', () => {
  it('(a) the law: diagrams identical up to free-port names share a fingerprint', () => {
    const mk = (a: string, b: string) => {
      const h = new DiagramBuilder()
      const n = h.termNode(h.root, p(`${a} ${b}`))
      const m = h.termNode(h.root, p('\\x. x'))
      h.wire(h.root, [
        { node: n, port: { kind: 'freeVar', name: a } },
        { node: m, port: { kind: 'output' } },
      ])
      return h.build()
    }
    expect(diagramFingerprint(mk('y', 'z'))).toBe(diagramFingerprint(mk('a', 'b')))
  })

  it('(b) mkDiagram renames node frees to s0… in first-occurrence order and rewrites endpoints to match', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('f (g f) h')) // first occurrences: f, g, h
    const m = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'g' } },
      { node: m, port: { kind: 'output' } },
    ])
    const d = h.build()
    expect(freePorts(termOf(d, n))).toEqual(['s0', 's1', 's2'])
    expect(freeVarEndpointNames(d, n)).toEqual(['s0', 's1', 's2'])
  })

  it('(c) canonicalizing a canonical diagram is the identity (node and wire objects reused)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('s0 s1'))
    const m = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 's0' } },
      { node: m, port: { kind: 'output' } },
    ])
    const d = h.build()
    const d2 = mkDiagram({
      root: d.root,
      regions: { ...d.regions },
      nodes: { ...d.nodes },
      wires: { ...d.wires },
    })
    for (const id of Object.keys(d.nodes)) expect(d2.nodes[id]).toBe(d.nodes[id])
    for (const id of Object.keys(d.wires)) expect(d2.wires[id]).toBe(d.wires[id])
  })

  it('(d) a canonical-name swap canonicalizes deterministically (simultaneous rename, no capture)', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('s1 s0')) // occurrence order s1, s0 → map {s1→s0, s0→s1}
    const hub = h.termNode(h.root, p('\\x. x'))
    const w = h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 's1' } },
      { node: hub, port: { kind: 'output' } },
    ])
    const d = h.build()
    expect(freePorts(termOf(d, n))).toEqual(['s0', 's1'])
    const ep = d.wires[w]!.endpoints.find((e) => e.node === n)!
    expect(ep.port).toEqual({ kind: 'freeVar', name: 's0' })
    // and the result is THE SAME diagram as one built with fresh names wired on the first port
    const ref = new DiagramBuilder()
    const rn = ref.termNode(ref.root, p('a b'))
    const rh = ref.termNode(ref.root, p('\\x. x'))
    ref.wire(ref.root, [
      { node: rn, port: { kind: 'freeVar', name: 'a' } },
      { node: rh, port: { kind: 'output' } },
    ])
    expect(diagramFingerprint(d)).toBe(diagramFingerprint(ref.build()))
  })

  it("(e) an endpoint naming a port absent from the node's term still fails with today's error", () => {
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'term', region: 'r0', term: p('x') } },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x' } }] },
        w2: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'zzz' } }] },
      },
    })).toThrowError(/non-existent port 'v:zzz' of node 'n0'/)
  })

  it('(e) an endpoint naming a canonical name that was NOT an original free is rejected, never aliased', () => {
    // frees = ['x'] → x becomes s0; an endpoint claiming 's0' referenced a
    // non-existent port of the ORIGINAL term and must not silently capture
    // the renamed one.
    expect(() => mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'term', region: 'r0', term: p('x') } },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x' } }] },
        w2: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 's0' } }] },
      },
    })).toThrowError(/non-existent port 'v:s0' of node 'n0'/)
  })

  it('(f) congruence join with the EMPTY certificate joins same-shape nodes built under different names', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, pS('SUCC q'))
    const n2 = h.termNode(h.root, pS('SUCC y'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'q' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const d = h.build()
    // after construction the two nodes carry literally equal terms
    expect(termEq(termOf(d, n1), termOf(d, n2))).toBe(true)
    const out = applyCongruenceJoin(d, n1, n2, empty)
    const shared = Object.values(out.wires).find(
      (w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2,
    )
    expect(shared).toBeDefined()
  })

  it('(g) deiteration accepts a copy built under different source names than its justifier', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('y'))
    const hub = h.termNode(h.root, p('\\x. x'))
    const cut = h.cut(h.root)
    const copy = h.termNode(cut, p('q')) // same shape as n, different source name
    h.wire(h.root, [
      { node: n, port: { kind: 'freeVar', name: 'y' } },
      { node: hub, port: { kind: 'output' } },
      { node: copy, port: { kind: 'freeVar', name: 'q' } },
    ])
    // a deiterable copy shares ALL boundary wires with its justifier,
    // including the output — exactly what iteration produces
    h.wire(h.root, [
      { node: n, port: { kind: 'output' } },
      { node: copy, port: { kind: 'output' } },
    ])
    const d = h.build()
    const sel = mkSelection(d, { region: cut, regions: [], nodes: [copy], wires: [] })
    const out = applyDeiteration(d, sel, 100)
    expect(out.nodes[copy]).toBeUndefined()
    const ref = new DiagramBuilder()
    const rn = ref.termNode(ref.root, p('y'))
    const rh = ref.termNode(ref.root, p('\\x. x'))
    ref.cut(ref.root)
    ref.wire(ref.root, [
      { node: rn, port: { kind: 'freeVar', name: 'y' } },
      { node: rh, port: { kind: 'output' } },
    ])
    expect(diagramFingerprint(out)).toBe(diagramFingerprint(ref.build()))
  })
})
