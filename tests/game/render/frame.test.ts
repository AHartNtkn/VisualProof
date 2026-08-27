import { describe, expect, it } from 'vitest'
import { SettledFrameTelemetry, formatFps, frameTiming, percentile } from '../../../src/game/render/frame'

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

describe('settled frame telemetry', () => {
  it('reports only frames observed after representation work settles', () => {
    const telemetry = new SettledFrameTelemetry(3)
    telemetry.record({ frameMs: 16, pending: 0, buildMs: 0, operations: 0 })
    telemetry.beginTransition()

    telemetry.record({ frameMs: 120, pending: 2, buildMs: 1.25, operations: 1 })
    telemetry.record({ frameMs: 80, pending: 0, buildMs: 2.75, operations: 1 })
    for (const frameMs of [17, 18, 19, 20]) {
      telemetry.record({ frameMs, pending: 0, buildMs: 0, operations: 0 })
    }

    expect(telemetry.snapshot()).toMatchObject({
      samples: [18, 19, 20],
      sampleCount: 3,
      transitionComplete: true,
    })
  })

  it('invalidates prior samples when camera-driven representation work occurs', () => {
    const telemetry = new SettledFrameTelemetry(3)
    for (const frameMs of [14, 15, 16]) {
      telemetry.record({ frameMs, pending: 0, buildMs: 0, operations: 0 })
    }

    telemetry.record({ frameMs: 90, pending: 0, buildMs: 5, operations: 1 })

    expect(telemetry.snapshot().samples).toEqual([])
  })
})
