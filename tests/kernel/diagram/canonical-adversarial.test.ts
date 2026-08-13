import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

describe('exploreForm adversarial graph battery', () => {
  it("distinguishes the scope of an atom's head wire", () => {
    const sig = relSig([])
    const make = (headAtOuter: boolean) => {
      const builder = new DiagramBuilder()
      const outer = builder.cut(builder.root)
      const inner = builder.cut(outer)
      const atom = builder.atom(inner, sig)
      builder.wire(
        [{ node: atom, port: { kind: 'head' } }],
        sig,
      )
      return builder.build()
    }

    expect(exploreForm(make(true))).not.toBe(exploreForm(make(false)))
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

    expect(exploreForm(make('first'))).toBe(exploreForm(make('second')))
    expect(exploreForm(make('first'))).not.toBe(exploreForm(make('both')))
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

    expect(exploreForm(make(false))).not.toBe(exploreForm(make(true)))
  })

  it('canonicalizes all permutations of three symmetric cuts', () => {
    const permutations = [
      [0, 1, 2], [0, 2, 1], [1, 0, 2],
      [1, 2, 0], [2, 0, 1], [2, 1, 0],
    ]
    const forms = permutations.map((permutation) => {
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
      return exploreForm(builder.build())
    })

    expect(new Set(forms).size).toBe(1)
  })

  it('distinguishes endpoint-free wire count and scope', () => {
    const make = (count: number, atRoot: boolean) => {
      const builder = new DiagramBuilder()
      const cut = builder.cut(builder.root)
      for (let index = 0; index < count; index++) {
        builder.wire( [])
      }
      return builder.build()
    }

    expect(exploreForm(make(1, false))).not.toBe(exploreForm(make(2, false)))
    expect(exploreForm(make(1, false))).not.toBe(exploreForm(make(1, true)))
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

    expect(exploreForm(ref('P'))).not.toBe(exploreForm(ref('Q')))
    expect(exploreForm(ref('P'))).not.toBe(exploreForm(atom(0)))
    expect(exploreForm(atom(0))).not.toBe(exploreForm(atom(1)))
  })
})
