import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { bareWire } from '../../fixtures/pins'

describe('sameDiagram adversarial graph battery', () => {
  it("distinguishes the scope of an atom's head wire", () => {
    const sig = relSig([])
    const make = (headAtOuter: boolean) => {
      const builder = new DiagramBuilder()
      const outer = builder.cut(builder.root)
      const inner = builder.cut(outer)
      const atom = builder.atom(inner, sig)
      const head = builder.wire(
        [{ node: atom, port: { kind: 'head' } }],
        sig,
      )
      builder.pin(head, headAtOuter ? outer : inner)
      return builder.build()
    }

    expect(sameDiagram(make(true), make(false))).toBe(false)
  })

  it('distinguishes one-sided from two-sided connectivity under symmetry', () => {
    const make = (side: 'first' | 'second' | 'both') => {
      const builder = new DiagramBuilder()
      const firstCut = builder.cut(builder.root)
      const secondCut = builder.cut(builder.root)
      const first = builder.ref(firstCut, 'Leaf', relSig([IOTA]))
      const second = builder.ref(secondCut, 'Leaf', relSig([IOTA]))
      const hub = builder.ref(builder.root, 'Hub', relSig([IOTA]))
      builder.wire( [
        { node: hub, port: { kind: 'arg', index: 0 } },
        ...(side === 'second'
          ? [{ node: second, port: { kind: 'arg' as const, index: 0 } }]
          : [{ node: first, port: { kind: 'arg' as const, index: 0 } }]),
        ...(side === 'both'
          ? [{ node: second, port: { kind: 'arg' as const, index: 0 } }]
          : []),
      ])
      return builder.build()
    }

    expect(sameDiagram(make('first'), make('second'))).toBe(true)
    expect(sameDiagram(make('first'), make('both'))).toBe(false)
  })

  it('distinguishes ordered argument roles on an atom', () => {
    const make = (swapped: boolean) => {
      const builder = new DiagramBuilder()
      const target = builder.atom(builder.root, relSig([IOTA, IOTA]))
      const left = builder.ref(builder.root, 'Left', relSig([IOTA]))
      const right = builder.ref(builder.root, 'Right', relSig([IOTA]))
      builder.wire( [
        { node: left, port: { kind: 'arg', index: 0 } },
        { node: target, port: { kind: 'arg', index: swapped ? 1 : 0 } },
      ])
      builder.wire( [
        { node: right, port: { kind: 'arg', index: 0 } },
        { node: target, port: { kind: 'arg', index: swapped ? 0 : 1 } },
      ])
      return builder.build()
    }

    expect(sameDiagram(make(false), make(true))).toBe(false)
  })

  it('canonicalizes all permutations of three symmetric cuts', () => {
    const permutations = [
      [0, 1, 2], [0, 2, 1], [1, 0, 2],
      [1, 2, 0], [2, 0, 1], [2, 1, 0],
    ]
    const diagrams = permutations.map((permutation) => {
      const builder = new DiagramBuilder()
      const cuts = [
        builder.cut(builder.root),
        builder.cut(builder.root),
        builder.cut(builder.root),
      ]
      const content = ['P', 'Q', 'R']
      permutation.forEach((cutIndex, contentIndex) => {
        builder.ref(cuts[cutIndex]!, content[contentIndex]!, relSig([]))
      })
      return builder.build()
    })

    for (const diagram of diagrams) {
      expect(sameDiagram(diagrams[0]!, diagram)).toBe(true)
    }
  })

  it('distinguishes endpoint-free wire count and scope', () => {
    const make = (count: number, atRoot: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      for (let index = 0; index < count; index++) {
        bareWire(builder, atRoot ? builder.root : cut)
      }
      return builder.build()
    }

    expect(sameDiagram(make(1, false), make(2, false))).toBe(false)
    expect(sameDiagram(make(1, false), make(1, true))).toBe(false)
  })

  it('distinguishes node kind, definition identity, and signature', () => {
    const ref = (defId: string) => {
      const builder = new DiagramBuilder()
      builder.ref(builder.root, defId, relSig([]))
      return builder.build()
    }
    const atom = (arity: number) => {
      const builder = new DiagramBuilder()
      builder.atom(
        builder.root,
        relSig(Array.from({ length: arity }, () => IOTA)),
      )
      return builder.build()
    }

    expect(sameDiagram(ref('P'), ref('Q'))).toBe(false)
    expect(sameDiagram(ref('P'), atom(0))).toBe(false)
    expect(sameDiagram(atom(0), atom(1))).toBe(false)
  })
})
