import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { campaignId, puzzleId } from '../../src/game/types'
import { twoVeils } from './fixtures'

const fixture = twoVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const puzzle = {
  id: puzzleId('two-veils'), campaign: campaign.id, title: 'Two Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: [{ rule: 'doubleCutElim' as const, region: fixture.eliminations[0]! }],
}

describe('verified game catalog', () => {
  it('accepts a closed puzzle whose backward witness reaches blank', () => {
    const catalog = buildCatalog({ campaigns: [campaign], puzzles: [puzzle], context: { relations: new Map() } })
    expect(catalog.puzzle(puzzle.id)).toBe(puzzle)
  })

  it('rejects missing prerequisites and dependency cycles', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzleId('missing')] }],
    })).toThrow(/missing prerequisite/)
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzle.id] }],
    })).toThrow(/dependency cycle/)
  })

  it('rejects a witness that does not reach blank', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, witness: [] }],
    })).toThrow(/witness does not reach blank/)
  })
})
