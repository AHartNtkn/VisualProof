import { describe, expect, it } from 'vitest'
import { canonicalArgOrder, defineRelation, inferFoldArgs } from '../../src/app/define'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { IOTA } from '../../src/kernel/diagram/sig'
import { findOccurrences } from '../../src/kernel/diagram/subgraph/match'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { extendRelations, verifyTheory } from '../../src/kernel/proof/context'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { BINARY, UNARY } from '../fixtures/zero-signature'
import { segment } from './helpers/build'

function definitionFixture() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, UNARY)
  const head = builder.wire([
    { node: atom, port: { kind: 'head' } },
  ], UNARY)
  // The head wire is internal to the definition, so the pin holding its
  // quantifier is part of the body too.
  const headPin = builder.pin(head, builder.root)
  const argument = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: diagram.root,
    regions: [],
    nodes: [atom, headPin],
    wires: [head],
  })
  return { diagram, selection, argument }
}

function boundedIdentityFixture(swap: boolean) {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const identity = builder.identity(cut, IOTA, 2)
  builder.wire([
    { node: identity, port: { kind: 'identity', index: swap ? 1 : 0 } },
  ])
  builder.wire([
    { node: identity, port: { kind: 'identity', index: swap ? 0 : 1 } },
  ])
  const diagram = builder.build()
  const selection = mkSelection(diagram, {
    region: cut,
    regions: [],
    nodes: [identity],
    wires: [],
  })
  return { diagram, cut, selection }
}

describe('structural relation definition', () => {
  it('registers and persists bounded identities independent of incidence indices', () => {
    const runs = [false, true].map((swap, index) => {
      const fixture = boundedIdentityFixture(swap)
      const name = `BoundedIdentity${index}`
      const empty = verifyTheory({ relations: [], theorems: [] })
      const { relation } = defineRelation(
        fixture.diagram,
        fixture.selection,
        name,
        empty,
      )
      const ctx = extendRelations(empty, [[name, relation]])
      const serialized = theoryToJson({
        relations: [[name, relation]],
        theorems: [],
      })
      const loaded = loadTheory(JSON.parse(JSON.stringify(serialized)))
      const stored = ctx.relations.get(name)!
      const reloaded = loaded.ctx.relations.get(name)!

      expect(stored.boundary).toHaveLength(2)
      expect(reloaded.boundary).toHaveLength(2)
      return {
        fixture,
        relation,
        form: exploreForm(reloaded.diagram, reloaded.boundary),
      }
    })

    expect(runs[1]!.form).toBe(runs[0]!.form)
    expect(findOccurrences(
      runs[1]!.fixture.diagram,
      runs[0]!.relation,
      { inRegion: runs[1]!.fixture.cut },
    ).matches).toHaveLength(2)
    expect(findOccurrences(
      runs[0]!.fixture.diagram,
      runs[1]!.relation,
      { inRegion: runs[0]!.fixture.cut },
    ).matches).toHaveLength(2)
  })

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
    const head = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const headPin = builder.pin(head, builder.root)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [atom, headPin], wires: [head],
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
      const head = builder.wire([
        { node: atom, port: { kind: 'head' } },
      ], UNARY)
      const headPin = builder.pin(head, builder.root)
      builder.wire([
        { node: atom, port: { kind: 'arg', index: 0 } },
      ])
      const extraRegion = builder.cut(builder.root)
      const extraWire = segment(builder, builder.root)
      const diagram = builder.build()
      const exact = mkSelection(diagram, {
        region: diagram.root, regions: [], nodes: [atom, headPin], wires: [head],
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
        nodes: extra === 'wire' ? [atom, headPin, ...extraWire.ends] : [atom, headPin],
        wires: extra === 'wire' ? [head, extraWire.wire] : [head],
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
