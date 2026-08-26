export type FrameTiming = {
  readonly sampleMs: number
  readonly movementSeconds: number
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
