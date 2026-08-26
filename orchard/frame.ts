export type FrameTiming = {
  readonly sampleMs: number
  readonly movementSeconds: number
}

export type SettledFrameRecord = {
  readonly frameMs: number
  readonly pending: number
  readonly buildMs: number
}

export type SettledFrameSnapshot = {
  readonly samples: readonly number[]
  readonly sampleCount: number
  readonly transitionBuildMs: number
  readonly transitionComplete: boolean
}

export class SettledFrameTelemetry {
  private readonly samples: number[] = []
  private previousPending = 0
  private transitionBuildMs = 0
  private transitionActive = false

  public constructor(private readonly windowSize: number) {
    if (!Number.isInteger(windowSize) || windowSize < 1) throw new Error('frame telemetry window must be a positive integer')
  }

  public beginTransition(): void {
    this.transitionBuildMs = 0
    this.transitionActive = true
  }

  public record(record: SettledFrameRecord): SettledFrameSnapshot {
    if (this.transitionActive) this.transitionBuildMs += record.buildMs
    const completedTransition = this.transitionActive && record.pending === 0
    const completedUnsolicitedDrain = !this.transitionActive && this.previousPending > 0 && record.pending === 0
    if (completedTransition) this.transitionActive = false

    if (completedTransition || completedUnsolicitedDrain) {
      this.samples.length = 0
    } else if (record.pending === 0) {
      this.samples.push(record.frameMs)
      if (this.samples.length > this.windowSize) this.samples.shift()
    }
    this.previousPending = record.pending
    return this.snapshot()
  }

  public snapshot(): SettledFrameSnapshot {
    return {
      samples: [...this.samples],
      sampleCount: this.samples.length,
      transitionBuildMs: this.transitionBuildMs,
      transitionComplete: !this.transitionActive,
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
