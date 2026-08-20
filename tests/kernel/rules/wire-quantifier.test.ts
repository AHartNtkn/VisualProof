import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { compileRelationSever } from '../../../src/kernel/proof/compile-content'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'
import { applyWireSever } from '../../../src/kernel/rules/wire-quantifier'
import { RuleError } from '../../../src/kernel/rules/error'
import { bareWire } from '../../fixtures/pins'

const UNARY = relSig([IOTA])

/**
 * Two applications of a shared unary signature wire at the root, each with
 * its own argument wire — the canonical abstraction fixture.
 */
function twoApplications() {
  const builder = new DiagramBuilder()
  const atomA = builder.atom(builder.root, UNARY)
  const atomB = builder.atom(builder.root, UNARY)
  builder.wire([
    { node: atomA, port: { kind: 'head' } },
    { node: atomB, port: { kind: 'head' } },
  ], UNARY)
  const argA = builder.wire([
    { node: atomA, port: { kind: 'arg', index: 0 } },
  ])
  const argB = builder.wire([
    { node: atomB, port: { kind: 'arg', index: 0 } },
  ])
  return { builder, atomA, atomB, argA, argB }
}

describe('relation abstraction refusals', () => {
  it('rejects an empty occurrence list', () => {
    const { builder } = twoApplications()
    const diagram = builder.build()

    expect(() => compileRelationSever(diagram, {
      scope: builder.root,
      occurrences: [],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/at least one occurrence/)
  })

  it('rejects overlapping selected content', () => {
    const { builder, atomA, argA } = twoApplications()
    const diagram = builder.build()
    const occurrence = {
      sel: { region: builder.root, regions: [], nodes: [atomA], wires: [] },
      args: [argA],
    }

    expect(() => compileRelationSever(diagram, {
      scope: builder.root,
      occurrences: [occurrence, occurrence],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/overlap/)
  })

  it('rejects occurrence regions outside the quantifier scope', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const inner = builder.cut(cut)
    const atom = builder.atom(inner, UNARY)
    builder.wire([{ node: atom, port: { kind: 'head' } }], UNARY)
    const arg = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => compileRelationSever(diagram, {
      scope: inner,
      occurrences: [{
        sel: { region: builder.root, regions: [], nodes: [], wires: [] },
        args: [arg],
      }],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/must descend from/)
  })

  it('rejects non-isomorphic pinned content across occurrences', () => {
    const { builder, atomA, atomB, argA, argB } = twoApplications()
    const noise = builder.ref(builder.root, 'Noise', relSig([]))
    const diagram = builder.build()

    expect(() => compileRelationSever(diagram, {
      scope: builder.root,
      occurrences: [
        {
          sel: { region: builder.root, regions: [], nodes: [atomA], wires: [] },
          args: [argA],
        },
        {
          sel: {
            region: builder.root,
            regions: [],
            nodes: [atomB, noise],
            wires: [],
          },
          args: [argB],
        },
      ],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(
      /not isomorphic under the same pinned content/,
    )
  })

  it('rejects a formal argument that does not touch the selected content', () => {
    const { builder, atomA } = twoApplications()
    const stray = bareWire(builder, builder.root)
    const diagram = builder.build()

    expect(() => compileRelationSever(diagram, {
      scope: builder.root,
      occurrences: [{
        sel: { region: builder.root, regions: [], nodes: [atomA], wires: [] },
        args: [stray],
      }],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/does not touch/)
  })

  it('rejects duplicate empty content at one site', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const empty = {
      sel: { region: builder.root, regions: [], nodes: [], wires: [] },
      args: [],
    }

    expect(() => compileRelationSever(diagram, {
      scope: builder.root,
      occurrences: [empty, empty],
    }, EMPTY_PROOF_CONTEXT)).toThrowError(/duplicate empty content/)
  })
})

describe('sever scope is bounded by the severed wire\'s scope', () => {
  /**
   * ¬[r1: ∃x pin(x) ¬[r2: ¬[r3: P(x) ¬[r4: P(x)]] ¬[r5: P(x) ¬[r6: P(x)]]]]
   *   = ∀x ((Px → Px) ∧ (Px → Px)); x is scoped at r1 (negative).
   */
  function forallFixture() {
    const P = relSig([IOTA])
    const b = new DiagramBuilder()
    const r1 = b.cut(b.root)
    const r2 = b.cut(r1)
    const r3 = b.cut(r2)
    const r4 = b.cut(r3)
    const r5 = b.cut(r2)
    const r6 = b.cut(r5)
    const p3 = b.atom(r3, P)
    const p4 = b.atom(r4, P)
    const p5 = b.atom(r5, P)
    const p6 = b.atom(r6, P)
    const head = b.wire([
      { node: p3, port: { kind: 'head' } }, { node: p4, port: { kind: 'head' } },
      { node: p5, port: { kind: 'head' } }, { node: p6, port: { kind: 'head' } },
    ], P)
    void head
    const arg = (node: string) => ({ node, port: { kind: 'arg', index: 0 } as const })
    const x = b.wire([arg(p3), arg(p4), arg(p5), arg(p6)])
    const pin = b.pin(x, r1)
    return { d: b.build(), x, r1, keep: [arg(p3), arg(p6), { node: pin, port: { kind: 'identity', index: 0 } as const }] }
  }

  it('refuses a fresh scope strictly above the wire\'s derived scope', () => {
    const { d, x, r1, keep } = forallFixture()
    expect(derivedScope(d, x)).toBe(r1)
    // The fresh scope must lie at-or-below the wire's own derived scope, not
    // merely pass the polarity gate — otherwise this would accept
    // ∀x φ(x,x) → ∃y ∀x φ(x,y).
    expect(() => applyWireSever(d, { wire: x, keep, scope: d.root })).toThrow(RuleError)
    expect(() => applyWireSever(d, { wire: x, keep, scope: d.root })).toThrow(/does not lie within/)
  })

  it('still accepts a fresh scope at or below the wire\'s scope (gated there)', () => {
    const { d, x, r1, keep } = forallFixture()
    // r1 is negative: forward sever refused by polarity, backward accepted.
    expect(() => applyWireSever(d, { wire: x, keep, scope: r1 })).toThrow(/requires a positive scope/)
    const out = applyWireSever(d, { wire: x, keep, scope: r1 }, 'backward')
    expect(derivedScope(out, x)).toBe(r1)
  })
})
