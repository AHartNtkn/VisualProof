import { describe, expect, it } from 'vitest'
import { formatFps, frameTiming } from '../../orchard/frame'

describe('frameTiming', () => {
  it('reports the full frame duration while bounding only movement catch-up', () => {
    expect(frameTiming(1350, 1000)).toEqual({ sampleMs: 350, movementSeconds: 0.1 })
    expect(frameTiming(1016, 1000)).toEqual({ sampleMs: 16, movementSeconds: 0.016 })
  })

  it('keeps a useful decimal below ten frames per second', () => {
    expect(formatFps(60.2)).toBe('60')
    expect(formatFps(4.25)).toBe('4.3')
    expect(formatFps(0.31)).toBe('0.3')
  })
})
