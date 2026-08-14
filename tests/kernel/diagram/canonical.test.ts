import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { bareWire } from '../../fixtures/pins'

describe('sameDiagram', () => {
  it('is invariant under construction order and id renaming', () => {
    const first = new DiagramBuilder()
    const firstCut = first.cut(first.root)
    const firstInner = first.ref(firstCut, 'Inner', relSig([IOTA]))
    const firstOuter = first.ref(first.root, 'Outer', relSig([IOTA]))
    first.wire( [
      { node: firstOuter, port: { kind: 'arg', index: 0 } },
      { node: firstInner, port: { kind: 'arg', index: 0 } },
    ])

    const second = new DiagramBuilder()
    const secondOuter = second.ref(second.root, 'Outer', relSig([IOTA]))
    const secondCut = second.cut(second.root)
    const secondInner = second.ref(secondCut, 'Inner', relSig([IOTA]))
    second.wire( [
      { node: secondInner, port: { kind: 'arg', index: 0 } },
      { node: secondOuter, port: { kind: 'arg', index: 0 } },
    ])

    expect(sameDiagram(first.build(), second.build())).toBe(true)
  })

  it('distinguishes shared and separate positional argument wires', () => {
    const make = (shared: boolean) => {
      const builder = new DiagramBuilder()
      const ref = builder.ref(builder.root, 'P', relSig([IOTA, IOTA]))
      if (shared) {
        builder.wire( [
          { node: ref, port: { kind: 'arg', index: 0 } },
          { node: ref, port: { kind: 'arg', index: 1 } },
        ])
      }
      return builder.build()
    }

    expect(sameDiagram(make(true), make(false))).toBe(false)
  })

  it('handles symmetric disconnected cuts by individualization', () => {
    const make = (swap: boolean) => {
      const builder = new DiagramBuilder()
      const first = builder.cut(builder.root)
      const second = builder.cut(builder.root)
      const [left, right] = swap ? [second, first] : [first, second]
      builder.ref(left, 'P', relSig([]))
      builder.ref(right, 'P', relSig([]))
      return builder.build()
    }

    expect(sameDiagram(make(false), make(true))).toBe(true)
  })

  it('distinguishes wire scope with otherwise identical endpoints', () => {
    const make = (atRoot: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      const ref = builder.ref(cut, 'P', relSig([IOTA]))
      const argument = builder.wire([
        { node: ref, port: { kind: 'arg', index: 0 } },
      ])
      builder.pin(argument, atRoot ? builder.root : cut)
      return builder.build()
    }

    expect(sameDiagram(make(true), make(false))).toBe(false)
  })

  it('pins boundary wires by order', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'P', relSig([IOTA, IOTA]))
    const first = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const second = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    expect(sameDiagram(diagram, diagram, [first, second], [second, first]))
      .toBe(false)
  })

  it('rejects a pinned wire that does not exist', () => {
    const builder = new DiagramBuilder()
    builder.ref(builder.root, 'P', relSig([]))
    const diagram = builder.build()
    expect(() => sameDiagram(diagram, diagram, ['ghost'], ['ghost']))
      .toThrowError(/pinned wire 'ghost' does not exist/)
  })

  it('records the complete ordered incidence vector of an aliased boundary', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'P', relSig([IOTA]))
    const exposed = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const bare = bareWire(builder, builder.root)
    const diagram = builder.build()

    expect(sameDiagram(
      diagram, diagram, [exposed, exposed, bare], [exposed, bare, exposed],
    )).toBe(false)
    expect(sameDiagram(
      diagram, diagram, [exposed, exposed, bare], [exposed, bare, bare],
    )).toBe(false)
  })
})

describe('sameDiagram signature-indexed content', () => {
  it('ignores insertion order for same-scope relational wires', () => {
    const unary = relSig([IOTA])
    const nullary = relSig([])
    const pinEnd = (node: string) => ({
      node,
      port: { kind: 'identity' as const, index: 0 },
    })
    const nodes = {
      unary: { kind: 'atom', region: 'r0', sig: unary },
      nullary: { kind: 'atom', region: 'r0', sig: nullary },
      unaryHeadPin: { kind: 'identity', region: 'r0', sig: unary, arity: 1 },
      nullaryHeadPin: { kind: 'identity', region: 'r0', sig: nullary, arity: 1 },
      unaryArgPin: { kind: 'identity', region: 'r0', sig: IOTA, arity: 1 },
    } as const
    const unaryHead = {
      sig: unary,
      endpoints: [
        { node: 'unary', port: { kind: 'head' as const } },
        pinEnd('unaryHeadPin'),
      ],
    }
    const nullaryHead = {
      sig: nullary,
      endpoints: [
        { node: 'nullary', port: { kind: 'head' as const } },
        pinEnd('nullaryHeadPin'),
      ],
    }
    const unaryArg = {
      sig: IOTA,
      endpoints: [
        { node: 'unary', port: { kind: 'arg' as const, index: 0 } },
        pinEnd('unaryArgPin'),
      ],
    }
    const forward = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { ...nodes },
      wires: { unaryHead, nullaryHead, unaryArg },
    })
    const reversed = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { ...nodes },
      wires: { nullaryHead, unaryHead, unaryArg },
    })

    expect(sameDiagram(forward, reversed)).toBe(true)
  })

  it('distinguishes wire signatures at the same scope', () => {
    const make = (arity: number) => {
      const builder = new DiagramBuilder()
      bareWire(
        builder,
        builder.root,
        relSig(Array.from({ length: arity }, () => IOTA)),
      )
      return builder.build()
    }

    expect(sameDiagram(make(0), make(1))).toBe(false)
    expect(sameDiagram(make(1), make(2))).toBe(false)
  })

  it('distinguishes exact reference content beyond graph shape', () => {
    const make = (defId: string) => {
      const builder = new DiagramBuilder()
      builder.ref(builder.root, defId, relSig([]))
      return builder.build()
    }

    expect(sameDiagram(make('P'), make('Q'))).toBe(false)
  })
})
