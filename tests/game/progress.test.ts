import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import { availableVellums, emptyProgress, isUnlocked, recordCompletion } from '../../src/game/progress'
import { puzzleId, type PuzzleDefinition } from '../../src/game/types'
import { minimalPuzzle, minimalSource } from './catalog-fixture'

const first = minimalPuzzle({ title: 'Two Veils' })
const second: PuzzleDefinition = {
  ...first, id: puzzleId('veil-retrieval'), title: 'Veil Retrieval',
  prerequisites: [first.id], grantsVellum: false,
}
const catalog = buildCatalog({ ...minimalSource(), puzzles: [first, second] })

describe('durable game progression', () => {
  it('records first completion immutably and makes repetition idempotent', () => {
    const empty = emptyProgress()
    const completed = recordCompletion(empty, first.id)
    expect(empty.completed.has(first.id)).toBe(false)
    expect(completed.completed.has(first.id)).toBe(true)
    expect(recordCompletion(completed, first.id)).toBe(completed)
  })

  it('unlocks a puzzle only after every prerequisite is complete', () => {
    expect(isUnlocked(catalog, emptyProgress(), first.id)).toBe(true)
    expect(isUnlocked(catalog, emptyProgress(), second.id)).toBe(false)
    expect(isUnlocked(catalog, recordCompletion(emptyProgress(), first.id), second.id)).toBe(true)
  })

  it('offers vellums only for completed puzzles that grant them', () => {
    let progress = recordCompletion(emptyProgress(), first.id)
    progress = recordCompletion(progress, second.id)
    expect([...availableVellums(catalog, progress)]).toEqual([first.id])
  })
})
