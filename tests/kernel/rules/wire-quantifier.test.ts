import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { compileRelationSever } from '../../../src/kernel/proof/compile-content'
import { EMPTY_PROOF_CONTEXT } from '../../../src/kernel/proof/context'

const UNARY = relSig([IOTA])

/**
 * Two applications of a shared unary signature wire at the root, each with
 * its own argument wire — the canonical abstraction fixture.
 */
function twoApplications() {
  const builder = new DiagramBuilder()
  const atomA = builder.atom(builder.root, UNARY)
  const atomB = builder.atom(builder.root, UNARY)
  builder.wire( [
    { node: atomA, port: { kind: 'head' } },
    { node: atomB, port: { kind: 'head' } },
  ], UNARY)
  const argA = builder.wire( [
    { node: atomA, port: { kind: 'arg', index: 0 } },
  ])
  const argB = builder.wire( [
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
    builder.wire( [{ node: atom, port: { kind: 'head' } }], UNARY)
    const arg = builder.wire( [
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
    const stray = builder.wire( [])
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
