import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { campaignId, puzzleId } from '../../src/game/types'
import { fourVeils, twoVeils } from './fixtures'

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

  it('fingerprints canonical relation content independently of map insertion order', () => {
    const other = fourVeils().goal
    const withRelations = (relations: ReadonlyMap<string, typeof fixture.goal>) => buildCatalog({
      campaigns: [campaign], puzzles: [puzzle], context: { relations },
    })

    const original = withRelations(new Map([['alpha', fixture.goal], ['beta', other]]))
    const reordered = withRelations(new Map([['beta', other], ['alpha', fixture.goal]]))
    const changed = withRelations(new Map([['alpha', fixture.goal], ['beta', fixture.goal]]))

    expect(reordered.fingerprint).toBe(original.fingerprint)
    expect(changed.fingerprint).not.toBe(original.fingerprint)
  })
})
