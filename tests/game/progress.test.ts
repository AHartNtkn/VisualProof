import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import {
  emptyProgress, isCultureUnlocked, isRequired, isUnlocked, recordCompletion,
} from '../../src/game/progress'
import { cultureId, puzzleId, type PuzzleDefinition } from '../../src/game/types'
import { minimalPuzzle, minimalSource } from './catalog-fixture'

const first = minimalPuzzle({ name: { professional: 'Two Veils' } })
const second: PuzzleDefinition = {
  ...first, id: puzzleId('veil-retrieval'), name: { professional: 'Veil Retrieval' },
  prerequisites: [first.id],
}
const third: PuzzleDefinition = {
  ...first, id: puzzleId('third-artifact'), name: { professional: 'Third Artifact' },
  prerequisites: [second.id],
}
const fourth: PuzzleDefinition = {
  ...first, id: puzzleId('fourth-artifact'), name: { professional: 'Fourth Artifact' },
  prerequisites: [third.id],
}
const fifth: PuzzleDefinition = {
  ...first, id: puzzleId('culture-gate'), name: { professional: 'Culture Gate' },
  prerequisites: [fourth.id],
}
const sixth: PuzzleDefinition = {
  ...first, id: puzzleId('elective-artifact'), name: { professional: 'Elective Artifact' },
}
const secondCulture = {
  ...minimalSource().cultures[0]!,
  id: cultureId('second-tradition'),
  name: 'Second tradition',
  relativeAge: 1,
  unlocksAfter: [fifth.id],
  gateway: puzzleId('second-gateway'),
}
const seventh: PuzzleDefinition = {
  ...first,
  id: secondCulture.gateway,
  culture: secondCulture.id,
  name: { professional: 'Second Gateway' },
}
const source = minimalSource()
const firstCulture = { ...source.cultures[0]!, gateway: first.id }
const catalog = buildCatalog({
  ...source,
  cultures: [firstCulture, secondCulture],
  puzzles: [first, second, third, fourth, fifth, sixth, seventh],
})

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

  it('unlocks a culture and its gateway-independent puzzles from completed gate artifacts', () => {
    expect(isCultureUnlocked(catalog, emptyProgress(), secondCulture.id)).toBe(false)
    const afterGate = recordCompletion(emptyProgress(), fifth.id)
    expect(isCultureUnlocked(catalog, afterGate, secondCulture.id)).toBe(true)
    expect(isUnlocked(catalog, afterGate, seventh.id)).toBe(true)
  })

  it('derives required puzzles from culture gates and their prerequisite closure', () => {
    expect(isRequired(catalog, sixth.id)).toBe(false)
    for (const required of [first, second, third, fourth, fifth, seventh]) {
      expect(isRequired(catalog, required.id)).toBe(true)
    }
  })
})
