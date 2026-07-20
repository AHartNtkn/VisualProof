import { diagramToJson } from '../../src/kernel/diagram/json'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { loadGameContent, type GameCatalog } from '../../src/game/catalog'
import {
  cultureId,
  puzzleId,
  type ArtifactName,
  type ArtifactProvenance,
  type CultureId,
  type GameRuleContext,
  type GameStep,
  type PuzzleId,
} from '../../src/game/types'
import { twoVeils } from './fixtures'

export type TestTeacherIntervention = {
  readonly id: string
  readonly trigger:
    | { readonly kind: 'opening' | 'completion' }
    | { readonly kind: 'recognizedUnwinnable'; readonly state: DiagramWithBoundary; readonly demonstration: readonly GameStep[] }
  readonly pages: readonly string[]
  readonly repeat: 'once' | 'repeatable'
  readonly recovery?: 'timeline'
}

export type TestPuzzleDefinition = {
  readonly id: PuzzleId
  readonly culture: CultureId
  readonly name: ArtifactName
  readonly provenance: ArtifactProvenance
  readonly goal: DiagramWithBoundary
  readonly prerequisites: readonly PuzzleId[]
  readonly witness: readonly GameStep[]
  readonly teacher: readonly TestTeacherIntervention[]
}

export type TestCultureDefinition = {
  readonly id: CultureId
  readonly name: string
  readonly shortName: string
  readonly relativeAge: number
  readonly historicalSummary: string
  readonly lineage: readonly CultureId[]
  readonly isolation: 'connected' | 'isolated' | 'uncertain'
  readonly sealingVocabulary: readonly string[]
  readonly unlocksAfter: readonly PuzzleId[]
  readonly gateway: PuzzleId
}

export type TestCatalogSource = {
  readonly cultures: readonly TestCultureDefinition[]
  readonly puzzles: readonly TestPuzzleDefinition[]
  readonly context: GameRuleContext
}

export const fixtureCultureId = cultureId('oldest-tradition')
export function minimalPuzzle(overrides: Partial<TestPuzzleDefinition> = {}): TestPuzzleDefinition {
  const fixture = twoVeils()
  return {
    id: puzzleId('two-veils'), culture: fixtureCultureId,
    name: { professional: 'Fixture artifact' },
    provenance: { summary: 'A fixture artifact used for catalog validation.', function: 'Supports a minimal verified witness.' },
    goal: fixture.goal, prerequisites: [],
    witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
    teacher: [{ id: 'opening-pair', trigger: { kind: 'opening' }, pages: ['Look for the nested pair.'], repeat: 'once' }],
    ...overrides,
  }
}

export function minimalSource(): TestCatalogSource {
  const puzzle = minimalPuzzle()
  return {
    cultures: [{
      id: fixtureCultureId, name: 'Fixture culture', shortName: 'Fixture', relativeAge: 0,
      historicalSummary: 'A fixture culture used for catalog validation.', lineage: [],
      isolation: 'connected', sealingVocabulary: ['veil'], unlocksAfter: [], gateway: puzzle.id,
    }],
    puzzles: [puzzle], context: { relations: new Map() },
  }
}

export function buildTestCatalog(source: TestCatalogSource): GameCatalog {
  const files: Record<string, unknown> = {
    'manifest.json': {
      format: 'cursebreaker-content', version: 3,
      puzzles: source.puzzles.map(({ id }) => `puzzles/${id}.json`),
      definitions: [...source.context.relations.keys()].sort().map((id) => `definitions/${id}.json`),
      progression: 'progression/core.json',
      coverage: Object.fromEntries(source.cultures.map(({ id }) => [id, `coverage/${id}.json`])),
      catalog: 'catalog/test.json', guidance: 'guidance/test.json',
    },
    'progression/core.json': {
      cultures: source.cultures.map((culture, order) => ({
        id: culture.id, order, unlocksAfter: culture.unlocksAfter, gateway: culture.gateway,
        puzzles: source.puzzles.filter((puzzle) => puzzle.culture === culture.id).map(({ id }) => id),
      })),
      placements: source.puzzles.map((puzzle) => ({
        puzzle: puzzle.id, prerequisites: puzzle.prerequisites,
      })),
    },
    'catalog/test.json': {
      cultures: source.cultures.map(({ unlocksAfter: _unlocksAfter, gateway: _gateway, ...culture }) => culture),
      artifacts: source.puzzles.map(({ id: puzzle, name, provenance }) => ({ puzzle, name, provenance })),
    },
    'guidance/test.json': {
      puzzles: source.puzzles.filter(({ teacher }) => teacher.length > 0).map((puzzle) => ({
        puzzle: puzzle.id,
        interventions: puzzle.teacher.map((intervention) => ({
          id: intervention.id,
          trigger: intervention.trigger.kind === 'recognizedUnwinnable'
            ? { kind: intervention.trigger.kind, state: diagramToJson(intervention.trigger.state.diagram) }
            : { kind: intervention.trigger.kind },
          repeat: intervention.repeat, pages: intervention.pages,
          ...(intervention.recovery === undefined ? {} : { recovery: intervention.recovery }),
        })),
      })),
    },
  }
  for (const culture of source.cultures) {
    files[`coverage/${culture.id}.json`] = {
      obligations: [{
        id: 'fixture-obligation', kind: 'isolated', family: 'fixture',
        distinction: 'Exercise the fixture proof.', stoppingRule: 'Stop after one fixture.',
      }],
      puzzles: source.puzzles.filter((puzzle) => puzzle.culture === culture.id).map(({ id: puzzle }) => ({
        puzzle, obligations: ['fixture-obligation'],
        visibleSituation: 'A fixture proof.', defeats: 'A fixture misconception.',
        experientialNeighbors: [],
      })),
    }
  }
  for (const puzzle of source.puzzles) files[`puzzles/${puzzle.id}.json`] = { id: puzzle.id, diagram: diagramToJson(puzzle.goal.diagram) }
  for (const [id, definition] of source.context.relations) files[`definitions/${id}.json`] = { id, diagram: diagramToJson(definition.diagram), boundary: definition.boundary }
  return loadGameContent(files)
}
