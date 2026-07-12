import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildCatalog } from '../../src/game/catalog'
import { openingCatalog, openingCatalogSource } from '../../src/game/content'
import { recordCompletion, emptyProgress } from '../../src/game/progress'
import { applyGameStep, moveCursor, startPuzzle } from '../../src/game/session'
import { loadGame, saveGame } from '../../src/game/save'
import { puzzleId, type PuzzleId } from '../../src/game/types'
import { minimalPuzzle, minimalSource } from './catalog-fixture'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle = minimalPuzzle({
  id: puzzleId('four-veils'), name: { professional: 'Four Veils' }, goal: fixture.goal,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
})
const source = minimalSource()
const catalog = buildCatalog({
  ...source,
  cultures: [{ ...source.cultures[0]!, gateway: puzzle.id }],
  puzzles: [puzzle],
})
const authority = {
  context: catalog.source.context,
  puzzle: (id: PuzzleId) => catalog.puzzle(id),
  canUseVellum: () => false,
}

describe('versioned game save', () => {
  it('round-trips the permanent four-veils artifact with all retained states after rewind', () => {
    const opening = openingCatalog()
    const fourVeils = opening.puzzle(puzzleId('four-veils'))
    const openingAuthority = {
      context: opening.source.context,
      puzzle: (id: PuzzleId) => opening.puzzle(id),
      canUseVellum: () => false,
    }
    let session = startPuzzle(fourVeils)
    for (const step of fourVeils.witness) {
      session = applyGameStep(session, step, openingAuthority).session
    }
    session = moveCursor(session, 1)
    const progress = recordCompletion(emptyProgress(), puzzleId('two-veils'))
    const encoded = saveGame(opening, progress, session)
    const loaded = loadGame(opening, JSON.parse(JSON.stringify(encoded)))
    expect([...loaded.progress.completed]).toEqual([puzzleId('two-veils')])
    expect(loaded.active?.timeline.states).toEqual(session.timeline.states)
    expect(loaded.active?.timeline.states).toHaveLength(3)
    expect(loaded.active?.timeline.steps).toEqual(fourVeils.witness)
    expect(loaded.active?.timeline.cursor).toBe(1)
  })

  it('refuses a permanent opening save when only cultural history drifts', () => {
    const opening = openingCatalog()
    const encoded = saveGame(opening, emptyProgress(), null)
    const source = openingCatalogSource()
    const changed = buildCatalog({
      ...source,
      cultures: source.cultures.map((culture, index) => index === 0
        ? { ...culture, historicalSummary: `${culture.historicalSummary} Changed.` }
        : culture),
    })

    expect(changed.fingerprint).not.toBe(opening.fingerprint)
    expect(() => loadGame(changed, encoded)).toThrow(/catalog fingerprint does not match/)
  })

  it('round-trips a term-bearing kernel step through its JSON wire format', () => {
    const step = {
      rule: 'closedTermIntro' as const,
      region: fixture.goal.diagram.root,
      term: parseTerm('\\x. x'),
    }
    const session = applyGameStep(startPuzzle(puzzle), step, authority).session
    const encoded = saveGame(catalog, emptyProgress(), session)
    expect(encoded.active?.steps[0]).toMatchObject({ rule: step.rule, term: expect.any(String) })
    const loaded = loadGame(catalog, JSON.parse(JSON.stringify(encoded)))
    expect(loaded.active?.timeline.steps).toEqual([step])
    expect(loaded.active?.timeline.states).toHaveLength(2)
    expect(loaded.active?.timeline.states[1]).toBeDefined()
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

  it('refuses an unknown rule before it can create an invalid timeline state', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: {
        puzzle: puzzle.id, cursor: 1,
        steps: [{ rule: 'unknown-rule' }],
      },
    })).toThrow(/invalid game step/)
  })

  it('refuses replay of an unavailable vellum', () => {
    const encoded = saveGame(catalog, emptyProgress(), null)
    expect(() => loadGame(catalog, {
      ...encoded,
      active: {
        puzzle: puzzle.id, cursor: 1,
        steps: [{ rule: 'vellumManifest', puzzle: puzzle.id, region: fixture.goal.diagram.root }],
      },
    })).toThrow(/solved seal .* is not available/)
  })
})
