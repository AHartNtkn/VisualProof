import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
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

  // NEEDS-ADJUDICATION: the closing assertion (the degenerate identity node
  // disappears) is eager-normalizer behavior. Identity nodes now persist and
  // only the explicit identification rule collapses them, so a join can no
  // longer remove one on its own.
  it('retains the outer wire and re-normalizes affected identity content', () => {
    // The identity sits below both wire scopes; the join degenerates it to
    // one wire.
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
    expect(joined.nodes[identity]).toBeUndefined()
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
