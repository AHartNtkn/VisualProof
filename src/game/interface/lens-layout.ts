export type LensLayout = {
  readonly left: number
  readonly top: number
  readonly size: number
  readonly glassInset: number
  readonly glassSize: number
}

export function lensLayout(width: number, height: number): LensLayout {
  const size = Math.max(1, Math.min(height - 32, width - 32))
  const glassInset = size * 0.135
  return {
    left: (width - size) / 2,
    top: (height - size) / 2,
    size,
    glassInset,
    glassSize: size - glassInset * 2,
  }
}
