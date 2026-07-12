import { cultureId, puzzleId, type GameCatalogSource, type PuzzleDefinition } from '../../src/game/types'
import { twoVeils } from './fixtures'

export const fixtureCultureId = cultureId('oldest-tradition')

export function minimalPuzzle(overrides: Partial<PuzzleDefinition> = {}): PuzzleDefinition {
  const fixture = twoVeils()
  return {
    id: puzzleId('two-veils'), culture: fixtureCultureId, title: 'Fixture artifact',
    goal: fixture.goal, prerequisites: [], grantsVellum: true,
    witness: [{ rule: 'doubleCutElim', region: fixture.eliminations[0]! }],
    ...overrides,
  }
}

export function minimalSource(): GameCatalogSource {
  return {
    cultures: [{ id: fixtureCultureId, name: 'Fixture culture' }],
    puzzles: [minimalPuzzle()], context: { relations: new Map() },
  }
}
