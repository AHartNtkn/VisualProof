import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { convertible } from '../../../src/kernel/term/convert'
import type { ConversionCertificate } from '../../../src/kernel/term/certificate'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { applyCongruenceJoin as kernelCongruenceJoin } from '../../../src/kernel/rules/congruence'
import { RuleError } from '../../../src/kernel/rules/error'
import { mapTermToCommonCarrier, proposePortCorrespondence, type PortCorrespondence } from '../../../src/kernel/rules/port-correspondence'
import type { Diagram, NodeId } from '../../../src/kernel/diagram/diagram'
import { termNodeAt } from '../../../src/kernel/rules/access'

const p = (s: string) => parseTerm(s)
const empty: ConversionCertificate = { leftSteps: [], rightSteps: [] }
const applyCongruenceJoin = (
  d: Diagram,
  a: NodeId,
  b: NodeId,
  certificate: ConversionCertificate,
  correspondence = proposePortCorrespondence(termNodeAt(d, a).term, termNodeAt(d, b).term),
) => kernelCongruenceJoin(d, a, b, certificate, correspondence)

const certFor = (l: string, r: string): ConversionCertificate => {
  const res = convertible(p(l), p(r), 256)
  if (res.status !== 'convertible') throw new Error(`test setup: '${l}' / '${r}' must be convertible`)
  return res.certificate
}

describe('congruence join (functionality of equality)', () => {
  it('requires one host wire only for ports assigned to the same common column', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('(\\u. kept) erasedLeft'))
    const n2 = h.termNode(h.root, p('(\\u. renamed) erasedRight'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'kept' } },
      { node: n2, port: { kind: 'freeVar', name: 'renamed' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'freeVar', name: 'erasedLeft' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'freeVar', name: 'erasedRight' } }])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const d = h.build()
    const correspondence: PortCorrespondence = {
      commonArity: 3,
      left: { s0: 0, s1: 1 },
      right: { s0: 0, s1: 2 },
    }
    const left = mapTermToCommonCarrier(
      (d.nodes[n1] as Extract<typeof d.nodes[string], { kind: 'term' }>).term,
      correspondence.left,
    )
    const right = mapTermToCommonCarrier(
      (d.nodes[n2] as Extract<typeof d.nodes[string], { kind: 'term' }>).term,
      correspondence.right,
    )
    const conversion = convertible(left, right, 256)
    if (conversion.status !== 'convertible') throw new Error('test setup requires mapped convertibility')
    expect(() => applyCongruenceJoin(d, n1, n2, conversion.certificate, correspondence)).not.toThrow()
  })

  it('joins outputs of two identical nodes whose shared free ports ride one wire', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f x'))
    const n2 = h.termNode(h.root, p('f x'))
    const wf = h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'f' } },
      { node: n2, port: { kind: 'freeVar', name: 'f' } },
    ])
    const wx = h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'x' } },
      { node: n2, port: { kind: 'freeVar', name: 'x' } },
    ])
    const o1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyCongruenceJoin(d, n1, n2, empty)
    const shared = Object.values(out.wires).find((w) =>
      w.endpoints.some((ep) => ep.node === n1 && ep.port.kind === 'output') &&
      w.endpoints.some((ep) => ep.node === n2 && ep.port.kind === 'output'))
    expect(shared).toBeDefined()
    expect(out.wires[o1]).toBeDefined() // outer/first wire survives as the merged one
    expect(out.wires[wf]!.endpoints).toHaveLength(2)
    expect(out.wires[wx]!.endpoints).toHaveLength(2)
  })

  it('joins βη-equal but distinct terms under a real certificate', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('f x'))
    const n2 = h.termNode(h.root, p('(\\u. f u) x'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'f' } },
      { node: n2, port: { kind: 'freeVar', name: 'f' } },
    ])
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'x' } },
      { node: n2, port: { kind: 'freeVar', name: 'x' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const d = h.build()
    const out = applyCongruenceJoin(d, n1, n2, certFor('f x', '(\\u. f u) x'))
    const shared = Object.values(out.wires).find((w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2)
    expect(shared).toBeDefined()
  })

  it('is polarity-blind: works inside a cut (negative region)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('g y'))
    const n2 = h.termNode(cut, p('g y'))
    h.wire(cut, [
      { node: n1, port: { kind: 'freeVar', name: 'g' } },
      { node: n2, port: { kind: 'freeVar', name: 'g' } },
    ])
    h.wire(cut, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(cut, [{ node: n1, port: { kind: 'output' } }])
    h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    const out = applyCongruenceJoin(h.build(), n1, n2, empty)
    const shared = Object.values(out.wires).find((w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2)
    expect(shared).toBeDefined()
    expect(shared!.scope).toBe(cut)
  })

  it('allows a bubble (quantifier, not negation) between the output scope and the region', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 1)
    const n1 = h.termNode(bub, p('c'))
    const n2 = h.termNode(bub, p('c'))
    h.wire(bub, [
      { node: n1, port: { kind: 'freeVar', name: 'c' } },
      { node: n2, port: { kind: 'freeVar', name: 'c' } },
    ])
    // outputs scoped at ROOT: only the bubble boundary lies between scope and region
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const out = applyCongruenceJoin(h.build(), n1, n2, empty)
    const shared = Object.values(out.wires).find((w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2)
    expect(shared).toBeDefined()
    expect(shared!.scope).toBe(h.root)
  })

  it('ignores free names present in only one term (they are quantified out by the certificate)', () => {
    // (λu. y) x ~βη y — x is irrelevant to the value, so it needs no wire agreement
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('(\\u. y) x'))
    const n2 = h.termNode(h.root, p('y'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'freeVar', name: 'x' } }])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const out = applyCongruenceJoin(h.build(), n1, n2, certFor('(\\u. y) x', 'y'))
    const shared = Object.values(out.wires).find((w) => w.endpoints.filter((ep) => ep.port.kind === 'output').length === 2)
    expect(shared).toBeDefined()
  })

  it('refuses nodes in different regions', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(h.root, p('y'))
    const n2 = h.termNode(cut, p('y'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    expect(() => applyCongruenceJoin(h.build(), n1, n2, empty)).toThrowError(/one region/)
  })

  it('refuses a shared free port riding two different wires', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('y'))
    const n2 = h.termNode(h.root, p('y'))
    h.wire(h.root, [{ node: n1, port: { kind: 'freeVar', name: 'y' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'freeVar', name: 'y' } }])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    // the nodes' source free 'y' is canonical s0 after construction
    expect(() => applyCongruenceJoin(h.build(), n1, n2, empty)).toThrowError(/common column 0.*'s0'/)
  })

  it('refuses a rejected certificate', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    expect(() => applyCongruenceJoin(h.build(), n1, n2, empty)).toThrowError(/certificate rejected/)
  })

  it('refuses when a cut separates an output scope from the nodes’ region', () => {
    // nodes in a cut, one output scoped at root: merging would move a
    // quantifier across the negation — the equality only holds inside it
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('y'))
    const n2 = h.termNode(cut, p('y'))
    h.wire(cut, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    expect(() => applyCongruenceJoin(h.build(), n1, n2, empty)).toThrowError(/no cut between/)
  })

  it('refuses joining a node with itself and refuses already-shared outputs', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. x'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'output' } },
      { node: n2, port: { kind: 'output' } },
    ])
    const d = h.build()
    expect(() => applyCongruenceJoin(d, n1, n1, empty)).toThrowError(/distinct nodes/)
    expect(() => applyCongruenceJoin(d, n1, n2, empty)).toThrowError(/already share/)
  })

  it('throws RuleError (gate vocabulary) for gate refusals', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(h.root, p('y'))
    const n2 = h.termNode(cut, p('y'))
    h.wire(h.root, [
      { node: n1, port: { kind: 'freeVar', name: 'y' } },
      { node: n2, port: { kind: 'freeVar', name: 'y' } },
    ])
    h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    expect(() => applyCongruenceJoin(h.build(), n1, n2, empty)).toThrowError(RuleError)
  })
})
