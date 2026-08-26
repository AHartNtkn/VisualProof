export type FrameTiming = {
  readonly sampleMs: number
  readonly movementSeconds: number
}

export type SettledFrameRecord = {
  readonly frameMs: number
  readonly pending: number
  readonly buildMs: number
  readonly operations: number
}

export type SettledFrameSnapshot = {
  readonly samples: readonly number[]
  readonly sampleCount: number
  readonly transitionBuildMs: number
  readonly transitionComplete: boolean
  readonly transitionGeneration: number
  readonly settledGeneration: number
}

export class SettledFrameTelemetry {
  private readonly samples: number[] = []
  private transitionBuildMs = 0
  private transitionActive = false
  private residencyActive = false
  private transitionGeneration = 0
  private settledGeneration = 0

  public constructor(private readonly windowSize: number) {
    if (!Number.isInteger(windowSize) || windowSize < 1) throw new Error('frame telemetry window must be a positive integer')
  }

  public beginTransition(): number {
    this.transitionBuildMs = 0
    this.transitionActive = true
    this.transitionGeneration++
    return this.transitionGeneration
  }

  public record(record: SettledFrameRecord): SettledFrameSnapshot {
    if (this.transitionActive) this.transitionBuildMs += record.buildMs
    const startsResidency = !this.residencyActive && (record.pending > 0 || record.operations > 0)
    const completesResidency = this.residencyActive && record.pending === 0
    const completedTransition = this.transitionActive && record.pending === 0
    const zeroWorkTransition = completedTransition && !this.residencyActive && record.operations === 0

    if (startsResidency || zeroWorkTransition) this.samples.length = 0
    if (startsResidency) this.residencyActive = true
    if (completedTransition) this.transitionActive = false
    if (this.residencyActive && record.pending === 0) this.residencyActive = false

    const drainBoundary = startsResidency || completesResidency || zeroWorkTransition
    if (!drainBoundary && record.pending === 0 && record.operations === 0) {
      this.samples.push(record.frameMs)
      if (this.samples.length > this.windowSize) this.samples.shift()
    }
    if (this.samples.length === this.windowSize && !this.transitionActive && !this.residencyActive) {
      this.settledGeneration = this.transitionGeneration
    }
    return this.snapshot()
  }

  public snapshot(): SettledFrameSnapshot {
    return {
      samples: [...this.samples],
      sampleCount: this.samples.length,
      transitionBuildMs: this.transitionBuildMs,
      transitionComplete: !this.transitionActive,
      transitionGeneration: this.transitionGeneration,
      settledGeneration: this.settledGeneration,
    }
  }
}

export function frameTiming(now: number, previous: number): FrameTiming {
  const sampleMs = Math.max(0, now - previous)
  return { sampleMs, movementSeconds: Math.min(sampleMs, 100) / 1000 }
}

export function formatFps(fps: number): string {
  return fps < 10 ? fps.toFixed(1) : fps.toFixed(0)
}

export function percentile(samples: readonly number[], fraction: number): number {
  if (samples.length === 0) return 0
  const sorted = [...samples].sort((a, b) => a - b)
  return sorted[Math.min(sorted.length - 1, Math.max(0, Math.ceil(sorted.length * fraction) - 1))]!
}
