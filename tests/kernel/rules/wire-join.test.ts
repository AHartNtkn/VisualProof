import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyWireJoin } from '../../../src/kernel/rules/wire-quantifier'

describe('iota wire join', () => {
  it('requires comparable scopes', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const first = builder.wire(firstCut, [])
    const second = builder.wire(secondCut, [])
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
    const outer = builder.wire(builder.root, [])
    const negativeInner = builder.wire(negative, [])
    const positiveInner = builder.wire(positive, [])
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

  it('retains the outer wire and re-normalizes affected identity content', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    const outerNode = builder.ref(builder.root, 'outer', relSig([IOTA]))
    const innerNode = builder.ref(cut, 'inner', relSig([IOTA]))
    const outer = builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: outerNode, port: { kind: 'arg', index: 0 } },
    ])
    const inner = builder.wire(cut, [
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
    const outer = builder.wire(builder.root, [
      { node: outerAtom, port: { kind: 'head' } },
    ], sig)
    const inner = builder.wire(cut, [
      { node: innerAtom, port: { kind: 'head' } },
    ], sig)
    builder.wire(builder.root, [{ node: outerAtom, port: { kind: 'arg', index: 0 } }])
    builder.wire(cut, [{ node: innerAtom, port: { kind: 'arg', index: 0 } }])
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
    const unary = builder.relWire(builder.root, relSig([IOTA]))
    const binary = builder.relWire(cut, relSig([IOTA, IOTA]))
    const diagram = builder.build()

    expect(() => applyWireJoin(diagram, { a: unary, b: binary }))
      .toThrowError(/equal signatures/)
  })
})
