import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { verifyTheory } from '../../src/kernel/proof/context'
import { applicableActions } from '../../src/app/actions'
import { identityInCut, tinyTheory, UNARY } from '../fixtures/zero-signature'
import { segment } from './helpers/build'
import {
  convertToHeadNormal,
  convertToNormal,
  convertToWeakHeadNormal,
} from '../../src/app/tactics'
import { applyStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'

const kinds = (
  diagram: Parameters<typeof applicableActions>[0],
  selection: Parameters<typeof applicableActions>[1],
  backward = false,
) => applicableActions(
  diagram,
  selection,
  verifyTheory(tinyTheory()),
  backward,
).map((action) => action.kind)

describe('applicableActions', () => {
  it('never offers identityInsert — equating is compositional (join, pin, expose)', () => {
    // Reuse the fixture that used to yield identityInsert for a selected
    // pair of same-signature wires under negative polarity: the descriptor
    // must never appear, in either orientation.
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = segment(builder, cut)
    const right = segment(builder, cut)
    const diagram = builder.build()

    const pair = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [...left.ends, ...right.ends],
      wires: [left.wire, right.wire],
    })
    expect(kinds(diagram, pair)).not.toContain('identityInsert')
    expect(kinds(diagram, pair, true)).not.toContain('identityInsert')

    const positiveBuilder = new DiagramBuilder()
    const positiveLeft = segment(positiveBuilder, positiveBuilder.root)
    const positiveRight = segment(positiveBuilder, positiveBuilder.root)
    const positive = positiveBuilder.build()
    const positivePair = mkSelection(positive, {
      region: positive.root,
      regions: [],
      nodes: [...positiveLeft.ends, ...positiveRight.ends],
      wires: [positiveLeft.wire, positiveRight.wire],
    })
    expect(kinds(positive, positivePair)).not.toContain('identityInsert')
    expect(kinds(positive, positivePair, true)).not.toContain('identityInsert')
  })

  it('does not offer a specialized action for a cut-contained disequality', () => {
    const exact = identityInCut()
    const enclosing = Object.entries(exact.regions)
      .find(([, region]) => region.kind === 'cut' && region.parent === exact.root)![0]
    expect(kinds(exact, mkSelection(exact, {
      region: exact.root,
      regions: [enclosing],
      nodes: [],
      wires: [],
    }))).not.toContain(['identity', 'Contradiction'].join(''))
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

  it('mirrors the orientation-aware erasure polarity matrix', () => {
    // Backward work is the SAME interface with polarity flipped: erasure is
    // offered exactly where the applier accepts it — positive regions going
    // forward, negative regions going backward. Nothing is suppressed.
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const negativeRef = builder.ref(cut, 'UnaryWitness', UNARY)
    const positiveRef = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const negativeSelection = mkSelection(diagram, {
      region: cut,
      regions: [],
      nodes: [negativeRef],
      wires: [],
    })
    const positiveSelection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [positiveRef],
      wires: [],
    })

    expect(kinds(diagram, positiveSelection)).toContain('erase')
    expect(kinds(diagram, negativeSelection)).not.toContain('erase')
    expect(kinds(diagram, negativeSelection, true)).toContain('erase')
    expect(kinds(diagram, positiveSelection, true)).not.toContain('erase')
  })

  it('offers only Phase-1 actions for a generic selected cut', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const first = builder.identity(cut, IOTA, 2)
    builder.wire([{ node: first, port: { kind: 'identity', index: 0 } }])
    builder.wire([{ node: first, port: { kind: 'identity', index: 1 } }])
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

  it('offers double-cut elimination and vacuity deletion only for their structural shapes', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    builder.cut(outer)
    const bare = segment(builder, builder.root, IOTA)
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
      nodes: [...bare.ends],
      wires: [bare.wire],
    }))).toContain('vacuityDelete')
  })

  it('does not offer relation quantifier menus or input descriptors', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const positiveContent = builder.ref(builder.root, 'Positive', relSig([]))
    const negativeContent = builder.ref(negative, 'Negative', relSig([]))
    const negativeRelation = segment(builder, negative, relSig([]))
    const positiveRelation = segment(builder, builder.root, relSig([]))
    const diagram = builder.build()

    const positiveOccurrence = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [positiveContent],
      wires: [],
    })
    expect(kinds(diagram, positiveOccurrence)).not.toContain('relationSever')
    expect(kinds(diagram, positiveOccurrence, true)).not.toContain('relationSever')

    const negativeOccurrence = mkSelection(diagram, {
      region: negative,
      regions: [],
      nodes: [negativeContent],
      wires: [],
    })
    expect(kinds(diagram, negativeOccurrence)).not.toContain('relationSever')
    expect(kinds(diagram, negativeOccurrence, true)).not.toContain('relationSever')

    const negativeWire = mkSelection(diagram, {
      region: negative,
      regions: [],
      nodes: [...negativeRelation.ends],
      wires: [negativeRelation.wire],
    })
    expect(kinds(diagram, negativeWire)).not.toContain('relationJoin')
    expect(kinds(diagram, negativeWire, true)).not.toContain('relationJoin')

    const positiveWire = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [...positiveRelation.ends],
      wires: [positiveRelation.wire],
    })
    expect(kinds(diagram, positiveWire)).not.toContain('relationJoin')
    expect(kinds(diagram, positiveWire, true)).not.toContain('relationJoin')
  })

  it('offers conversion only for exactly one whole term node', () => {
    const builder = new DiagramBuilder()
    const term = builder.term(builder.root, parseTerm('(\\x. x) y').term, 1)
    const ref = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const termSelection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [term],
      wires: [],
    })
    const mixedSelection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [term, ref],
      wires: [],
    })

    expect(kinds(diagram, termSelection)).toContain('convert')
    expect(kinds(diagram, termSelection, true)).toContain('convert')
    expect(kinds(diagram, mixedSelection)).not.toContain('convert')
  })
})

describe('Lambda conversion tactics', () => {
  it.each([
    {
      name: 'normal',
      source: 'f ((\\x. x) y)',
      target: 'f y',
      convert: convertToNormal,
    },
    {
      name: 'head-normal',
      source: '\\z. (\\x. x) y',
      target: '\\z. y',
      convert: convertToHeadNormal,
    },
    {
      name: 'weak-head-normal',
      source: '(\\x. x) y',
      target: 'y',
      convert: convertToWeakHeadNormal,
    },
  ])('emits a checked, replayable $name conversion', ({ source, target, convert }) => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm(source)
    const node = builder.term(
      builder.root,
      parsed.term,
      parsed.freeIdentifiers.length,
    )
    const diagram = builder.build()
    const context = verifyTheory(tinyTheory())

    const tactic = convert(diagram, node, 64)
    expect(tactic.step).toMatchObject({
      rule: 'lambdaConversion',
      node,
      term: parseTerm(target).term,
    })
    expect(applyStep(diagram, tactic.step, context)).toEqual(tactic.diagram)
  })

  it('refuses exhausted and no-op normalization instead of committing unchecked output', () => {
    const normalBuilder = new DiagramBuilder()
    const normal = normalBuilder.term(normalBuilder.root, parseTerm('f0').term, 1)
    const normalDiagram = normalBuilder.build()
    expect(() => convertToNormal(normalDiagram, normal, 64)).toThrow(/already.*normal form/i)

    const omegaBuilder = new DiagramBuilder()
    const omega = omegaBuilder.term(
      omegaBuilder.root,
      parseTerm('(\\x. x x) (\\x. x x)').term,
      0,
    )
    const omegaDiagram = omegaBuilder.build()
    expect(() => convertToNormal(omegaDiagram, omega, 1)).toThrow(/fuel/i)
  })

  it('authors normalization from the free slots used by the reduct', () => {
    const builder = new DiagramBuilder()
    const parsed = parseTerm('(\\x. kept) discarded')
    const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
    const source = builder.build()
    const discardedWire = Object.entries(source.wires).find(([, wire]) =>
      wire.endpoints.some((endpoint) => (
        endpoint.node === node
        && endpoint.port.kind === 'free'
        && endpoint.port.index === 1
      )))![0]

    const conversion = convertToNormal(source, node, 64)
    const target = conversion.diagram.nodes[node]
    const context = verifyTheory(tinyTheory())

    expect(conversion.step.rule).toBe('lambdaConversion')
    expect(applyStep(source, conversion.step, context)).toEqual(conversion.diagram)
    expect(target?.kind).toBe('term')
    if (target?.kind !== 'term') throw new Error('normalization lost the term node')
    expect(target.freeArity).toBe(1)
    expect(target.term).toEqual(parseTerm('kept').term)
    expect(source.wires[discardedWire]!.endpoints).toHaveLength(2)
    expect(conversion.diagram.wires[discardedWire]!.endpoints).toHaveLength(2)
    expect(conversion.diagram.wires[discardedWire]!.endpoints.every((endpoint) => (
      conversion.diagram.nodes[endpoint.node]?.kind === 'identity'
    ))).toBe(true)
  })
})
