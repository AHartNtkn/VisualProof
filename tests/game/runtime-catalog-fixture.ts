import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import { freePorts } from '../../src/kernel/term/term'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { applyStep } from '../../src/kernel/proof/step'
import { applyConversion } from '../../src/kernel/rules/conversion'
import { proposePortCorrespondence } from '../../src/kernel/rules/port-correspondence'
import { weakHeadNormalize } from '../../src/kernel/term/hnf'
import type { GameCatalog } from '../../src/game/catalog'
import {
  beginComprehensionDraft,
  currentComprehensionDraft,
  materializeComprehensionSnapshot,
} from '../../src/game/interface/loupe/draft'
import {
  cultureId,
  puzzleId,
} from '../../src/game/types'
import { controllerSource, FIRST_CULTURE, SECOND_CULTURE } from './controller-fixture'
import { buildTestCatalog, minimalPuzzle, minimalSource, type TestCatalogSource, type TestPuzzleDefinition, type TestTeacherIntervention } from './catalog-fixture'

const evidence = new Map<string, { witness: TestPuzzleDefinition['witness']; teacher: readonly TestTeacherIntervention[] }>()
const remember = (source: TestCatalogSource): TestCatalogSource => {
  for (const puzzle of source.puzzles) evidence.set(puzzle.id, { witness: puzzle.witness, teacher: puzzle.teacher })
  return source
}
export const runtimeEvidenceFor = (id: string) => evidence.get(id)

export const ARTIFACT = puzzleId('vacuous-record')
export const MANIFEST_HOST = puzzleId('manifest-host')
export const DISSOLVE_HOST = puzzleId('dissolve-host')

export function artifactRuntimeCatalog(): GameCatalog {
  const base = minimalSource()
  const artifactBuilder = new DiagramBuilder()
  const bubble = artifactBuilder.bubble(artifactBuilder.root, 0)
  const artifactGoal = mkDiagramWithBoundary(artifactBuilder.build(), [])
  const artifact = minimalPuzzle({
    id: ARTIFACT,
    name: { professional: 'Vacuous record' },
    goal: artifactGoal,
    witness: [{ rule: 'vacuousElim', region: bubble }],
  })
  const manifest = minimalPuzzle({
    id: MANIFEST_HOST,
    name: { professional: 'Manifest host' },
    prerequisites: [ARTIFACT],
  })
  const dissolve = minimalPuzzle({
    ...artifact,
    id: DISSOLVE_HOST,
    name: { professional: 'Dissolve host' },
    prerequisites: [ARTIFACT],
  })
  return buildTestCatalog(remember({
    ...base,
    cultures: [{ ...base.cultures[0]!, gateway: ARTIFACT }],
    puzzles: [artifact, manifest, dissolve],
  }))
}

export function longRuntimeCatalog(): GameCatalog {
  const base = controllerSource()
  const cultures = [FIRST_CULTURE, SECOND_CULTURE] as const
  const puzzles: TestPuzzleDefinition[] = []
  for (const [cultureIndex] of cultures.entries()) {
    const template = base.puzzles[cultureIndex]!
    for (let index = 0; index < 8; index += 1) {
      puzzles.push({
        ...template,
        id: puzzleId(`long-${cultureIndex}-${index}`),
        name: { professional: `Long record ${cultureIndex}-${index}` },
        prerequisites: [],
      })
    }
  }
  return buildTestCatalog(remember({
    ...base,
    cultures: base.cultures.map((culture, index) => ({
      ...culture,
      gateway: puzzles[index * 8]!.id,
    })),
    puzzles,
  }))
}

export const MOTION_PUZZLE = puzzleId('motion-interaction')

export const EDITOR_PUZZLE = puzzleId('editor-interaction')

export function editorRuntimeCatalog(): GameCatalog {
  const base = minimalSource()
  const builder = new DiagramBuilder()
  const bubble = builder.bubble(builder.root, 0)
  builder.atom(bubble, bubble)
  const outer = builder.cut(builder.root)
  builder.cut(outer)
  const term = builder.termNode(outer, parseTerm('x'))
  const diagram = builder.build()
  const draft = beginComprehensionDraft(diagram, bubble)
  const materialized = materializeComprehensionSnapshot(
    currentComprehensionDraft(draft), draft.host, draft.bubble,
  )
  const instantiate = {
    rule: 'comprehensionInstantiate' as const,
    bubble,
    comp: materialized.relation,
    attachments: materialized.attachments,
    binders: [],
  }
  const afterInstantiation = applyStep(
    diagram,
    instantiate,
    EMPTY_PROOF_CONTEXT,
    'backward',
  )
  const termWires = Object.entries(afterInstantiation.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === term))
    .map(([wire]) => wire)
  const eraseTerm = {
    rule: 'erasure' as const,
    sel: mkSelection(afterInstantiation, {
      region: outer, regions: [], nodes: [term], wires: termWires,
    }),
  }
  const puzzle = minimalPuzzle({
    id: EDITOR_PUZZLE,
    name: { professional: 'Editor interaction' },
    goal: mkDiagramWithBoundary(diagram, []),
    witness: [instantiate, eraseTerm, { rule: 'doubleCutElim', region: outer }],
  })
  return buildTestCatalog(remember({
    ...base,
    cultures: [{ ...base.cultures[0]!, gateway: EDITOR_PUZZLE }],
    puzzles: [puzzle],
  }))
}

export function motionRuntimeCatalog(): GameCatalog {
  const base = minimalSource()
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  builder.cut(outer)
  const third = builder.cut(outer)
  builder.cut(third)
  const term = builder.termNode(outer, parseTerm('(\\a. a) ((\\b. b) ((\\c. c) q))'))
  const diagram = builder.build()
  const first = { rule: 'doubleCutElim' as const, region: third }
  const afterFirst = applyStep(diagram, first, EMPTY_PROOF_CONTEXT, 'backward')
  const termValue = afterFirst.nodes[term]
  if (termValue?.kind !== 'term') throw new Error('motion fixture term disappeared')
  const target = weakHeadNormalize(termValue.term, 256).term
  const correspondence = proposePortCorrespondence(
    termValue.term,
    target,
    termValue.freePorts,
    freePorts(target),
  )
  const conversion = applyConversion(afterFirst, term, target, correspondence, 256)
  const convert = {
    rule: 'conversion' as const,
    node: term,
    term: target,
    certificate: conversion.certificate,
    correspondence,
    attachments: {},
  }
  const afterConversion = applyStep(
    afterFirst,
    convert,
    EMPTY_PROOF_CONTEXT,
    'backward',
  )
  const termWires = Object.entries(afterConversion.wires)
    .filter(([, wire]) => wire.endpoints.some((endpoint) => endpoint.node === term))
    .map(([wire]) => wire)
  const erase = {
    rule: 'erasure' as const,
    sel: mkSelection(afterConversion, {
      region: outer, regions: [], nodes: [term], wires: termWires,
    }),
  }
  const puzzle = minimalPuzzle({
    id: MOTION_PUZZLE,
    name: { professional: 'Motion interaction' },
    goal: mkDiagramWithBoundary(diagram, []),
    witness: [first, convert, erase, { rule: 'doubleCutElim', region: outer }],
  })
  return buildTestCatalog(remember({
    ...base,
    cultures: [{ ...base.cultures[0]!, id: cultureId('motion-culture'), gateway: MOTION_PUZZLE }],
    puzzles: [{ ...puzzle, culture: cultureId('motion-culture') }],
  }))
}
