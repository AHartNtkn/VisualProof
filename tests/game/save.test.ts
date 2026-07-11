import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { recordCompletion, emptyProgress } from '../../src/game/progress'
import { applyGameStep, moveCursor, startPuzzle } from '../../src/game/session'
import { loadGame, saveGame } from '../../src/game/save'
import { campaignId, puzzleId, type PuzzleDefinition, type PuzzleId } from '../../src/game/types'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const puzzle: PuzzleDefinition = {
  id: puzzleId('four-veils'), campaign: campaign.id, title: 'Four Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
}
const catalog = buildCatalog({ campaigns: [campaign], puzzles: [puzzle], context: { relations: new Map() } })
const authority = {
  context: catalog.source.context,
  puzzle: (id: PuzzleId) => catalog.puzzle(id),
  canUseVellum: () => false,
}

describe('versioned game save', () => {
  it('round-trips sorted completion ids and a rewound retained timeline', () => {
    let session = startPuzzle(puzzle)
    for (const step of puzzle.witness) session = applyGameStep(session, step, authority).session
    session = moveCursor(session, 1)
    const progress = recordCompletion(emptyProgress(), puzzle.id)
    const encoded = saveGame(catalog, progress, session)
    expect(encoded.completed).toEqual([puzzle.id])
    const loaded = loadGame(catalog, JSON.parse(JSON.stringify(encoded)))
    expect([...loaded.progress.completed]).toEqual([puzzle.id])
    expect(loaded.active?.timeline.states).toHaveLength(3)
    expect(loaded.active?.timeline.cursor).toBe(1)
  })

  it('refuses catalog drift and unknown completion ids', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, { ...encoded, catalogFingerprint: 'drifted' }))
      .toThrow(/catalog fingerprint does not match/)
    expect(() => loadGame(catalog, { ...encoded, completed: ['unknown-puzzle'] }))
      .toThrow(/unknown puzzle/)
  })

  it('refuses an invalid cursor and a forged proof-assistant step', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: { puzzle: puzzle.id, steps: [], cursor: 2 },
    })).toThrow(/active cursor/)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: {
        puzzle: puzzle.id, cursor: 1,
        steps: [{ rule: 'theorem', name: 'forged', direction: 'forward', at: {} }],
      },
    })).toThrow(/unknown theorem|invalid game step/)
  })
})
