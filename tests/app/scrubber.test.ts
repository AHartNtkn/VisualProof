import { describe, expect, it } from 'vitest'
import { cursorCommand, nearestTimelineCursor, tickStatus, timelineCopy } from '../../src/app/interact/scrubber'

describe('temporal rail helpers', () => {
  it('maps every coordinate to the nearest clamped tick without dead zones', () => {
    expect(nearestTimelineCursor(-50, 100, 400, 5)).toBe(0)
    expect(nearestTimelineCursor(100, 100, 400, 5)).toBe(0)
    expect(nearestTimelineCursor(249, 100, 400, 5)).toBe(1)
    expect(nearestTimelineCursor(500, 100, 400, 5)).toBe(4)
    expect(nearestTimelineCursor(900, 100, 400, 5)).toBe(4)
    expect(nearestTimelineCursor(100, 100, 0, 1)).toBe(0)
  })

  it('classifies retained history around the current cursor', () => {
    expect([0, 1, 2, 3, 4].map((index) => tickStatus(index, 2))).toEqual([
      'past', 'past', 'current', 'future', 'future',
    ])
  })

  it('uses one cursor decision for controls and keyboard shortcuts', () => {
    expect(cursorCommand(2, 5, 'undo')).toBe(1)
    expect(cursorCommand(2, 5, 'redo')).toBe(3)
    expect(cursorCommand(0, 5, 'undo')).toBeNull()
    expect(cursorCommand(4, 5, 'redo')).toBeNull()
  })

  it('formats current/final position and the transition label', () => {
    expect(timelineCopy(0, 3, [])).toBe('0 / 2 · start')
    expect(timelineCopy(2, 3, ['wrap', 'cite lemma'])).toBe('2 / 2 · cite lemma')
  })
})
