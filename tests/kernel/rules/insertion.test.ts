import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { applyInsertion, applyWireJoin } from '../../../src/kernel/rules/insertion'

const p = (s: string) => parseTerm(s)

function closedPattern() {
  const b = new DiagramBuilder()
  b.termNode(b.root, p('\\x. x'))
  return mkDiagramWithBoundary(b.build(), [])
}

describe('applyInsertion', () => {
  it('splices into a negative region', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const host = h.build()
    const out = applyInsertion(host, cut, closedPattern(), [])
    const nodesInCut = Object.values(out.nodes).filter((n) => n.region === cut)
    expect(nodesInCut).toHaveLength(1)
  })

  it('rejects positive regions by name', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const cut2 = h.cut(cut)
    const host = h.build()
    expect(() => applyInsertion(host, host.root, closedPattern(), []))
      .toThrowError(/insertion requires a negative region; 'r0' is positive/)
    expect(() => applyInsertion(host, cut2, closedPattern(), []))
      .toThrowError(/insertion requires a negative region; 'r2' is positive/)
  })

  it('rejects unknown regions', () => {
    const h = new DiagramBuilder()
    const host = h.build()
    expect(() => applyInsertion(host, 'ghost', closedPattern(), []))
      .toThrowError(/unknown region 'ghost'/)
  })

  it('bubbles do not affect the polarity gate', () => {
    const h = new DiagramBuilder()
    const bub = h.bubble(h.root, 0)          // still positive
    const cut = h.cut(bub)                   // depth 1: negative
    const bubInCut = h.bubble(cut, 0)        // still negative
    const host = h.build()
    expect(() => applyInsertion(host, bub, closedPattern(), []))
      .toThrowError(/insertion requires a negative region/)
    expect(() => applyInsertion(host, cut, closedPattern(), [])).not.toThrow()
    expect(() => applyInsertion(host, bubInCut, closedPattern(), [])).not.toThrow()
  })
})

describe('applyWireJoin', () => {
  function twoWireHost() {
    // cut holds two nodes; their output wires are both scoped at the cut
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(cut, p('\\x. \\y. x'))
    const w1 = h.wire(cut, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    return { host: h.build(), cut, w1, w2 }
  }

  it('merges two wires when the inner scope is negative', () => {
    const { host, w1, w2 } = twoWireHost()
    const out = applyWireJoin(host, w1, w2)
    expect(out.wires[w2]).toBeUndefined()
    expect(out.wires[w1]?.endpoints).toHaveLength(2)
  })

  it('keeps the outer scope when scopes differ (inner gate)', () => {
    // w1 scoped at root (positive), w2 scoped at the cut (negative):
    // join is gated on the INNER scope, and the merged wire keeps ROOT scope
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const n1 = h.termNode(cut, p('\\x. x'))
    const n2 = h.termNode(cut, p('\\x. \\y. x'))
    const w1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cut, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    const out = applyWireJoin(host, w1, w2)
    expect(out.wires[w1]?.scope).toBe(host.root)
    expect(out.wires[w1]?.endpoints).toHaveLength(2)
    expect(out.wires[w2]).toBeUndefined()
  })

  it('rejects joins whose inner scope is positive, by name', () => {
    const h = new DiagramBuilder()
    const n1 = h.termNode(h.root, p('\\x. x'))
    const n2 = h.termNode(h.root, p('\\x. \\y. x'))
    const w1 = h.wire(h.root, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(h.root, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireJoin(host, w1, w2))
      .toThrowError(/joining wires requires the inner wire's scope to be negative; 'r0' is positive/)
  })

  it('rejects when the inner scope is positive even though the outer is negative', () => {
    const h = new DiagramBuilder()
    const cut1 = h.cut(h.root)        // depth 1: negative
    const cut2 = h.cut(cut1)          // depth 2: positive
    const n1 = h.termNode(cut1, p('\\x. x'))
    const n2 = h.termNode(cut2, p('\\x. \\y. x'))
    const w1 = h.wire(cut1, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cut2, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireJoin(host, w1, w2))
      .toThrowError(new RegExp(`inner wire's scope to be negative; '${cut2}' is positive`))
  })

  it('rejects incomparable scopes and identical wires, by name', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const cutB = h.cut(h.root)
    const n1 = h.termNode(cutA, p('\\x. x'))
    const n2 = h.termNode(cutB, p('\\x. x'))
    const w1 = h.wire(cutA, [{ node: n1, port: { kind: 'output' } }])
    const w2 = h.wire(cutB, [{ node: n2, port: { kind: 'output' } }])
    const host = h.build()
    expect(() => applyWireJoin(host, w1, w2))
      .toThrowError(/incomparable scopes/)
    expect(() => applyWireJoin(host, w1, w1))
      .toThrowError(/cannot join a wire with itself/)
  })
})
