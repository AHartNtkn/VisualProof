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
  it('excludes drain frames, resets on completion, and retains summed transition build CPU', () => {
    const telemetry = new SettledFrameTelemetry(60)
    telemetry.record({ frameMs: 16, pending: 0, buildMs: 0, operations: 0 })
    telemetry.beginTransition()

    telemetry.record({ frameMs: 120, pending: 2, buildMs: 1.25, operations: 1 })
    expect(telemetry.snapshot()).toMatchObject({ sampleCount: 0, transitionBuildMs: 1.25, transitionComplete: false })
    telemetry.record({ frameMs: 80, pending: 0, buildMs: 2.75, operations: 1 })

    expect(telemetry.snapshot()).toMatchObject({
      samples: [],
      sampleCount: 0,
      transitionBuildMs: 4,
      transitionComplete: true,
    })
    telemetry.record({ frameMs: 20, pending: 0, buildMs: 0, operations: 0 })
    expect(telemetry.snapshot().samples).toEqual([20])
  })

  it('resets a zero-work transition and caps the complete post-drain window at 60 samples', () => {
    const telemetry = new SettledFrameTelemetry(60)
    for (let frame = 1; frame <= 60; frame++) telemetry.record({ frameMs: frame, pending: 0, buildMs: 0, operations: 0 })
    expect(telemetry.snapshot().sampleCount).toBe(60)

    telemetry.beginTransition()
    telemetry.record({ frameMs: 999, pending: 0, buildMs: 0, operations: 0 })
    expect(telemetry.snapshot()).toMatchObject({ sampleCount: 0, transitionBuildMs: 0, transitionComplete: true })

    for (let frame = 1; frame <= 61; frame++) telemetry.record({ frameMs: frame, pending: 0, buildMs: 0, operations: 0 })
    expect(telemetry.snapshot().samples).toEqual(Array.from({ length: 60 }, (_, index) => index + 2))
  })

  it('resets settled samples after camera-driven residency work drains', () => {
    const telemetry = new SettledFrameTelemetry(60)
    telemetry.record({ frameMs: 16, pending: 0, buildMs: 0, operations: 0 })
    telemetry.record({ frameMs: 90, pending: 1, buildMs: 3, operations: 1 })
    expect(telemetry.snapshot().samples).toEqual([])

    telemetry.record({ frameMs: 70, pending: 0, buildMs: 2, operations: 1 })

    expect(telemetry.snapshot().samples).toEqual([])
    expect(telemetry.snapshot().transitionBuildMs).toBe(0)
  })

  it('invalidates settled samples for camera work that starts and finishes in one frame exactly once', () => {
    const telemetry = new SettledFrameTelemetry(3)
    for (const frameMs of [14, 15, 16]) telemetry.record({ frameMs, pending: 0, buildMs: 0, operations: 0 })

    telemetry.record({ frameMs: 90, pending: 0, buildMs: 5, operations: 1 })
    expect(telemetry.snapshot().samples).toEqual([])
    telemetry.record({ frameMs: 17, pending: 0, buildMs: 0, operations: 0 })
    telemetry.record({ frameMs: 18, pending: 0, buildMs: 0, operations: 0 })

    expect(telemetry.snapshot().samples).toEqual([17, 18])
  })

  it('publishes the new settled generation atomically with its sixtieth sample', () => {
    const telemetry = new SettledFrameTelemetry(60)
    expect(telemetry.beginTransition()).toBe(1)
    telemetry.record({ frameMs: 100, pending: 0, buildMs: 1, operations: 1 })
    for (let frame = 1; frame <= 59; frame++) telemetry.record({ frameMs: frame, pending: 0, buildMs: 0, operations: 0 })
    expect(telemetry.snapshot()).toMatchObject({
      sampleCount: 59,
      transitionGeneration: 1,
      settledGeneration: 0,
    })

    const settled = telemetry.record({ frameMs: 60, pending: 0, buildMs: 0, operations: 0 })
    expect(settled).toMatchObject({ sampleCount: 60, transitionGeneration: 1, settledGeneration: 1 })

    expect(telemetry.beginTransition()).toBe(2)
    expect(telemetry.snapshot()).toMatchObject({ transitionGeneration: 2, settledGeneration: 1 })
  })
})
