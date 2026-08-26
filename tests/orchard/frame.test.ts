import { describe, expect, it } from 'vitest'
import { formatFps, frameTiming, percentile } from '../../orchard/frame'

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

describe('percentile', () => {
  it('uses the literal nearest-rank sample without mutating its input', () => {
    const samples = [30, 10, 40, 20]

    expect(percentile(samples, 0)).toBe(10)
    expect(percentile(samples, 0.25)).toBe(10)
    expect(percentile(samples, 0.5)).toBe(20)
    expect(percentile(samples, 0.95)).toBe(40)
    expect(percentile(samples, 1)).toBe(40)
    expect(samples).toEqual([30, 10, 40, 20])
  })

  it('returns zero for an empty rolling window', () => {
    expect(percentile([], 0.95)).toBe(0)
  })
})
