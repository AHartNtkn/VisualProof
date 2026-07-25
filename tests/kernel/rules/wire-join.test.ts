import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { RuleError } from '../../../src/kernel/rules/error'
import { applyWireJoin } from '../../../src/kernel/rules/wire-join'

describe('wire join: signature gate', () => {
  it('refuses to join a IOTA wire with a relSig([IOTA]) wire, naming both sigs', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a = h.wire(cut, [], IOTA)
    const b = h.wire(cut, [], relSig([IOTA]))
    const d = h.build()
    expect(() => applyWireJoin(d, a, b))
      .toThrowError(/cannot join wires of different signatures: 'i' vs '\(i\)'/)
    expect(() => applyWireJoin(d, b, a)).toThrow(RuleError)
  })

  it('refuses to join two structurally distinct relational wires', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a = h.wire(cut, [], relSig([IOTA]))
    const b = h.wire(cut, [], relSig([IOTA, IOTA]))
    const d = h.build()
    expect(() => applyWireJoin(d, a, b))
      .toThrowError(/cannot join wires of different signatures: '\(i\)' vs '\(i,i\)'/)
  })

  it('the sig gate fires before scope comparability, so an incomparable-scope pair with mismatched sigs reports the sig mismatch', () => {
    const h = new DiagramBuilder()
    const cutA = h.cut(h.root)
    const cutB = h.cut(h.root)
    const a = h.wire(cutA, [], IOTA)
    const b = h.wire(cutB, [], relSig([IOTA]))
    const d = h.build()
    expect(() => applyWireJoin(d, a, b))
      .toThrowError(/cannot join wires of different signatures/)
  })

  it('same-sig wires with comparable scopes still succeed (gate does not over-refuse)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a = h.wire(h.root, [], IOTA)
    const b = h.wire(cut, [], IOTA)
    const d = h.build()
    const out = applyWireJoin(d, a, b)
    expect(out.wires[a]).toBeDefined()
    expect(out.wires[b]).toBeUndefined()
    expect(out.wires[a]!.endpoints).toHaveLength(0)
    expect(out.wires[a]!.sig).toEqual(IOTA)
  })
})
