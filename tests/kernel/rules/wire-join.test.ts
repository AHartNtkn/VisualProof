import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyVacuityDelete } from '../../../src/kernel/rules/identity-rules'
import { applyWireJoin } from '../../../src/kernel/rules/wire-quantifier'
import { bareWire } from '../../fixtures/pins'

describe('iota wire join', () => {
  it('requires comparable scopes', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const first = bareWire(builder, firstCut)
    const second = bareWire(builder, secondCut)
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, {
      a: first,
      b: second,
    })).toThrowError(/incomparable scopes/)
  })

  it('requires negative inner scope forward and positive inner scope backward', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positive = builder.cut(negative)
    const outer = bareWire(builder, builder.root)
    const negativeInner = bareWire(builder, negative)
    const positiveInner = bareWire(builder, positive)
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, {
      a: outer,
      b: negativeInner,
    })).not.toThrow()
    expect(() => applyWireJoin(diagram, {
      a: outer,
      b: positiveInner,
    })).toThrowError(/inner wire's scope to be negative/)
    expect(() => applyWireJoin(diagram, {
      a: outer,
      b: positiveInner,
    }, 'backward')).not.toThrow()
  })

  it('retains the outer wire and leaves the degenerate identity for vacuity', () => {
    // The identity sits below both wire scopes, so the join leaves both its
    // ports on one wire: it now asserts only x = x.
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const deep = builder.cut(cut)
    const identity = builder.identity(deep, IOTA, 2)
    const outerNode = builder.ref(builder.root, 'outer', relSig([IOTA]))
    const innerNode = builder.ref(cut, 'inner', relSig([IOTA]))
    const outer = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: outerNode, port: { kind: 'arg', index: 0 } },
    ])
    const inner = builder.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
      { node: innerNode, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    expect(diagram.nodes[identity]).toBeDefined()

    const joined = applyWireJoin(diagram, {
      a: outer,
      b: inner,
    })

    expect(joined.wires[outer]).toBeDefined()
    expect(joined.wires[inner]).toBeUndefined()
    expect(joined.wires[outer]!.endpoints).toEqual(expect.arrayContaining([
      { node: outerNode, port: { kind: 'arg', index: 0 } },
      { node: innerNode, port: { kind: 'arg', index: 0 } },
    ]))
    // The join moves incidences; it does not rewrite equality apparatus. Both
    // of the identity's ports now sit on the merged wire, a loop.
    expect(joined.nodes[identity]).toEqual({
      kind: 'identity',
      region: deep,
      sig: IOTA,
      arity: 2,
    })
    expect(joined.wires[outer]!.endpoints.filter((endpoint) =>
      endpoint.node === identity)).toHaveLength(2)

    // x = x is ⊤-shaped, so vacuity detaches it — and may, because the merged
    // wire keeps the two real ends that fix its derived scope at the root.
    const cleaned = applyVacuityDelete(joined, {
      nodes: { [identity]: { region: deep, sig: IOTA, arity: 2 } },
      wires: {},
      attachments: {
        [outer]: [
          { node: identity, port: { kind: 'identity', index: 0 } },
          { node: identity, port: { kind: 'identity', index: 1 } },
        ],
      },
    })

    expect(cleaned.nodes[identity]).toBeUndefined()
    expect(cleaned.wires[outer]!.endpoints).toEqual([
      { node: outerNode, port: { kind: 'arg', index: 0 } },
      { node: innerNode, port: { kind: 'arg', index: 0 } },
    ])
    expect(derivedScope(cleaned, outer)).toBe(builder.root)
  })
})

describe('generalized wire join', () => {
  it('merges relation wires of equal signature under a negative inner scope', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const sig = relSig([IOTA])
    const outerAtom = builder.atom(builder.root, sig)
    const innerAtom = builder.atom(cut, sig)
    const outer = builder.wire([
      { node: outerAtom, port: { kind: 'head' } },
    ], sig)
    const inner = builder.wire([
      { node: innerAtom, port: { kind: 'head' } },
    ], sig)
    builder.wire([{ node: outerAtom, port: { kind: 'arg', index: 0 } }])
    builder.wire([{ node: innerAtom, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()

    const joined = applyWireJoin(diagram, { a: outer, b: inner })

    expect(joined.wires[inner]).toBeUndefined()
    expect(joined.wires[outer]!.endpoints).toEqual(expect.arrayContaining([
      { node: outerAtom, port: { kind: 'head' } },
      { node: innerAtom, port: { kind: 'head' } },
    ]))
  })

  it('rejects joining wires of different signatures', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const unary = bareWire(builder, builder.root, relSig([IOTA]))
    const binary = bareWire(builder, cut, relSig([IOTA, IOTA]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, { a: unary, b: binary }))
      .toThrowError(/equal signatures/)
  })
})
