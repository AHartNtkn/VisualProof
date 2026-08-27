import { describe, expect, it } from 'vitest'
import { application, free } from '../../../src/kernel/term/term'
import {
  compactFreeInterface,
  defaultFreeIdentifier,
  freeIdentifierSlot,
  freeSlots,
  mapFreeSlots,
} from '../../../src/kernel/term/interface'

describe('nameless term interfaces', () => {
  it('owns free-slot traversal and remapping in first-occurrence order', () => {
    const term = application(free(2), application(free(0), free(2)))

    expect(freeSlots(term)).toEqual([2, 0])
    expect(mapFreeSlots(term, [1, 0, 3])).toEqual(
      application(free(3), application(free(1), free(3))),
    )
  })

  it('compacts a term through the unique physical carriers it actually uses', () => {
    const term = application(free(2), application(free(0), free(1)))

    expect(compactFreeInterface(term, ['shared', 'shared', 'other'])).toEqual({
      term: application(free(0), application(free(1), free(1))),
      carriers: ['other', 'shared'],
      sourceSlots: [2, 0],
    })
  })

  it('owns the canonical textual spelling of positional free slots', () => {
    expect(defaultFreeIdentifier(12)).toBe('f12')
    expect(freeIdentifierSlot('f12')).toBe(12)
    expect(freeIdentifierSlot('free12')).toBeNull()
  })
})
