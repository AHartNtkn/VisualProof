import { describe, expect, it } from 'vitest'
import { defineRelation, inferFoldArgs } from '../../src/app/define'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { verifyTheory } from '../../src/kernel/proof/context'
import { UNARY } from '../fixtures/zero-signature'

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
      [fixture.argument],
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
      [fixture.argument],
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
})
