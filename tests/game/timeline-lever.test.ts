import { describe, expect, it } from 'vitest'
import { leverCursorAt, leverHandleFraction } from '../../src/game/interface/timeline-lever'

describe('timeline lever presentation', () => {
  it('maps retained states to the full physical track', () => {
    expect(leverHandleFraction(0, 5)).toBe(0)
    expect(leverHandleFraction(2, 5)).toBe(0.5)
    expect(leverHandleFraction(4, 5)).toBe(1)
    expect(leverHandleFraction(0, 1)).toBe(0.5)
  })

  it('delegates pointer mapping to the established temporal rail rule', () => {
    expect(leverCursorAt(250, 100, 300, 4)).toBe(2)
  })
})
