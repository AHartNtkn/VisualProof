import { describe, expect, it } from 'vitest'
import { canonicalArgOrder, defineRelation, inferFoldArgs } from '../../src/app/define'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { verifyTheory } from '../../src/kernel/proof/context'
import { BINARY, UNARY } from '../fixtures/zero-signature'

function definitionFixture() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, UNARY)
  const head = builder.wire(builder.root, [
    { node: atom, port: { kind: 'head' } },
  ], UNARY)
  const argument = builder.wire(builder.root, [
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: diagram.root,
    regions: [],
    nodes: [atom],
    wires: [head],
  })
  return { diagram, selection, argument }
}

describe('structural relation definition', () => {
  it('extracts an exact ordered boundary and infers the same fold attachment', () => {
    const fixture = definitionFixture()
    const { relation } = defineRelation(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    const ctx = verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] })
    expect(relation.boundary).toHaveLength(1)
    expect(inferFoldArgs(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      ctx,
    )).toEqual([fixture.argument])
  })

  it('reports exact structural mismatch without conversion advice', () => {
    const fixture = definitionFixture()
    const { relation } = defineRelation(
      fixture.diagram,
      fixture.selection,
      'LocalUnary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    const empty = new DiagramBuilder().build()
    const emptySelection = mkSelection(empty, {
      region: empty.root, regions: [], nodes: [], wires: [],
    })
    expect(() => inferFoldArgs(
      empty,
      emptySelection,
      'LocalUnary',
      verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] }),
    )).toThrow('the selection must match the definition exactly.')
  })

  it('uses canonical boundary order as the sole definition order', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, BINARY)
    const head = builder.wire(builder.root, [
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire(builder.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [atom], wires: [head],
    })
    const canonical = canonicalArgOrder(diagram, selection)
    const { relation } = defineRelation(
      diagram,
      selection,
      'CanonicalBinary',
      verifyTheory({ relations: [], theorems: [] }),
    )
    expect(canonical).toHaveLength(2)
    expect(relation.boundary).toHaveLength(2)

    const legacy = defineRelation as unknown as (
      d: typeof diagram,
      s: typeof selection,
      order: readonly string[],
      name: string,
      context: ReturnType<typeof verifyTheory>,
    ) => unknown
    expect(() => legacy(
      diagram,
      selection,
      [...canonical].reverse(),
      'ManualBinary',
      verifyTheory({ relations: [], theorems: [] }),
    )).toThrow(/manual boundary order is not supported/)
  })

  it.each(['region', 'wire'] as const)(
    'rejects an exact occurrence padded with an extra selected %s',
    (extra) => {
      const builder = new DiagramBuilder()
      const atom = builder.atom(builder.root, UNARY)
      const head = builder.wire(builder.root, [
        { node: atom, port: { kind: 'head' } },
      ], UNARY)
      builder.wire(builder.root, [
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      const extraRegion = builder.cut(builder.root)
      const extraWire = builder.wire(builder.root, [])
      const diagram = builder.build()
      const exact = mkSelection(diagram, {
        region: diagram.root, regions: [], nodes: [atom], wires: [head],
      })
      const { relation } = defineRelation(
        diagram,
        exact,
        'LocalUnary',
        verifyTheory({ relations: [], theorems: [] }),
      )
      const padded = mkSelection(diagram, {
        region: diagram.root,
        regions: extra === 'region' ? [extraRegion] : [],
        nodes: [atom],
        wires: extra === 'wire' ? [head, extraWire] : [head],
      })
      expect(() => inferFoldArgs(
        diagram,
        padded,
        'LocalUnary',
        verifyTheory({ relations: [['LocalUnary', relation]], theorems: [] }),
      )).toThrow('the selection must match the definition exactly.')
    },
  )
})
