import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { verifyTheory } from '../../src/kernel/proof/context'
import { applicableActions } from '../../src/app/actions'
import { identityInCut, tinyTheory, UNARY } from '../fixtures/zero-signature'

const kinds = (
  diagram: Parameters<typeof applicableActions>[0],
  selection: Parameters<typeof applicableActions>[1],
) => applicableActions(diagram, selection, verifyTheory(tinyTheory())).map((action) => action.kind)

describe('applicableActions', () => {
  it('offers identity insertion only for two or more homogeneous selected wires in a negative region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = builder.wire(cut, [])
    const right = builder.wire(cut, [])
    const relation = builder.wire(cut, [], relSig([]))
    const diagram = builder.build()

    const pair = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [],
      wires: [left, right],
    })
    expect(kinds(diagram, pair)).toContain('identityInsert')

    const singleton = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [],
      wires: [left],
    })
    expect(kinds(diagram, singleton)).not.toContain('identityInsert')

    const mixed = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [],
      wires: [left, relation],
    })
    expect(kinds(diagram, mixed)).not.toContain('identityInsert')

    const positiveBuilder = new DiagramBuilder()
    const positiveLeft = positiveBuilder.wire(positiveBuilder.root, [])
    const positiveRight = positiveBuilder.wire(positiveBuilder.root, [])
    const positive = positiveBuilder.build()
    expect(kinds(positive, mkSelection(positive, {
      region: positive.root,
      regions: [],
      nodes: [],
      wires: [positiveLeft, positiveRight],
    }))).not.toContain('identityInsert')
  })

  it('offers identity contradiction only for the exact direct asserted/negated identity shape', () => {
    const exact = identityInCut()
    const enclosing = Object.entries(exact.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === exact.root)![0]
    expect(kinds(exact, mkSelection(exact, {
      region: exact.root,
      regions: [enclosing],
      nodes: [],
      wires: [],
    }))).toContain('identityContradiction')

    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    expect(kinds(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    }))).not.toContain('identityContradiction')

    const nearMissBuilder = new DiagramBuilder()
    const nearMissEnclosing = nearMissBuilder.cut(nearMissBuilder.root)
    const nearMissChild = nearMissBuilder.cut(nearMissEnclosing)
    const equality = nearMissBuilder.identity(nearMissEnclosing, IOTA, 2)
    const disequality = nearMissBuilder.identity(nearMissChild, IOTA, 2)
    const unrelated = nearMissBuilder.ref(nearMissChild, 'unrelated', relSig([]))
    nearMissBuilder.wire(nearMissBuilder.root, [
      { node: equality, port: { kind: 'identity', index: 0 } },
      { node: disequality, port: { kind: 'identity', index: 0 } },
    ])
    nearMissBuilder.wire(nearMissBuilder.root, [
      { node: equality, port: { kind: 'identity', index: 1 } },
      { node: disequality, port: { kind: 'identity', index: 1 } },
    ])
    const nearMiss = nearMissBuilder.build()
    expect(kinds(nearMiss, mkSelection(nearMiss, {
      region: nearMiss.root,
      regions: [nearMissEnclosing],
      nodes: [],
      wires: [],
    }))).not.toContain('identityContradiction')
    expect(nearMiss.nodes[unrelated]).toBeDefined()
  })

  it('keeps generic structural actions, fold/unfold, and theorem citation', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [ref],
      wires: [],
    })
    const actions = applicableActions(diagram, selection, verifyTheory(tinyTheory()))
    expect(actions.map((action) => action.kind)).toEqual(expect.arrayContaining([
      'erase',
      'doubleCutWrap',
      'iterate',
      'deiterate',
      'relUnfold',
      'relFold',
      'citeTheorem',
    ]))
    expect(actions.find((action) => action.kind === 'citeTheorem')).toMatchObject({
      name: 'StructuralReflexivity',
      direction: 'forward',
    })
    expect(actions.every((action) => action.label.length > 0)).toBe(true)
  })

  it('does not invent backward erasure in a physically negative region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const ref = builder.ref(cut, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [ref],
      wires: [],
    })
    const actions = applicableActions(
      diagram,
      selection,
      verifyTheory(tinyTheory()),
      true,
    )
    expect(actions.map((action) => action.kind)).not.toContain('erase')
  })

  it('offers only Phase-1 actions for a generic selected cut', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.identity(cut, IOTA, 2)
    builder.wire(builder.root, [{ node: first, port: { kind: 'identity', index: 0 } }])
    builder.wire(builder.root, [{ node: first, port: { kind: 'identity', index: 1 } }])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    })
    expect(kinds(diagram, selection)).toEqual([
      'erase',
      'doubleCutWrap',
      'iterate',
      'deiterate',
      'relFold',
      'citeTheorem',
    ])
  })

  it('offers double-cut elimination and vacuous elimination only for their structural shapes', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    builder.cut(outer)
    const bare = builder.wire(builder.root, [], IOTA)
    const diagram = builder.build()
    expect(kinds(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [outer],
      nodes: [],
      wires: [],
    }))).toContain('doubleCutElim')
    expect(kinds(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [],
      wires: [bare],
    }))).toContain('vacuousElim')
  })
})
