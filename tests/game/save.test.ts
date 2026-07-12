import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildCatalog } from '../../src/game/catalog'
import { recordCompletion, emptyProgress } from '../../src/game/progress'
import { applyGameStep, moveCursor, startPuzzle } from '../../src/game/session'
import { loadGame, saveGame } from '../../src/game/save'
import { puzzleId, type PuzzleId } from '../../src/game/types'
import { minimalPuzzle, minimalSource } from './catalog-fixture'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle = minimalPuzzle({
  id: puzzleId('four-veils'), title: 'Four Veils', goal: fixture.goal,
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
