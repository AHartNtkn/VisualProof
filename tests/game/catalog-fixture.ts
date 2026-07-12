import {
  cultureId,
  performanceId,
  puzzleId,
  type GameCatalogSource,
  type PerformanceDefinition,
  type PuzzleDefinition,
} from '../../src/game/types'
import { twoVeils } from './fixtures'

export const fixtureCultureId = cultureId('oldest-tradition')
export const fixturePerformanceId = performanceId('remove-double-cut')

export function minimalPerformance(
  overrides: Partial<PerformanceDefinition> = {},
): PerformanceDefinition {
  return {
    id: fixturePerformanceId,
    description: 'Remove a double cut.',
    prerequisites: [],
    knowledgePoints: [
      {
        id: 'recognize-double-cut',
        instruction: 'Find two nested cuts with nothing between them.',
        commonError: 'Selecting only one of the cuts.',
        correction: 'Trace both cut boundaries before acting.',
      },
      {
        id: 'remove-both-cuts',
        instruction: 'Remove the nested pair together.',
        commonError: 'Changing the contents of the inner region.',
        correction: 'Preserve the inner contents while removing both boundaries.',
      },
    ],
    masteryEvidence: 'Removes a double cut without altering its contents.',
    remediation: [],
    ...overrides,
  }
}

export function minimalPuzzle(overrides: Partial<PuzzleDefinition> = {}): PuzzleDefinition {
  const fixture = twoVeils()
  return {
    id: puzzleId('two-veils'), culture: fixtureCultureId,
    name: { professional: 'Fixture artifact' },
    provenance: {
      summary: 'A fixture artifact used for catalog validation.',
      function: 'Supports a minimal verified witness.',
    },
    goal: fixture.goal, prerequisites: [], grantsVellum: true,
    witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
    learning: {
      introduces: [fixturePerformanceId], practices: [], retrieves: [], assesses: [],
      rulesUsed: ['doubleCutElim'],
    },
    teacher: [{ trigger: 'opening', text: 'Look for the nested pair.' }],
    misconceptions: [],
    ...overrides,
  }
}

export function minimalSource(): GameCatalogSource {
  const puzzle = minimalPuzzle()
  return {
    cultures: [{
      id: fixtureCultureId, name: 'Fixture culture', relativeAge: 0,
      historicalSummary: 'A fixture culture used for catalog validation.',
      lineage: [], isolation: 'connected', sealingVocabulary: ['veil'],
      unlocksAfter: [], gateway: puzzle.id,
    }],
    performances: [minimalPerformance()], puzzles: [puzzle], context: { relations: new Map() },
  }
}
