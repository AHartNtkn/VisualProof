export type LodLevel = 'full' | 'reduced' | 'marker' | 'culled'

const BANDS = { full: 140, reduced: 20, marker: 2 } as const
const HYSTERESIS = 0.15

export function projectedDiameterPx(radius: number, depth: number, viewportHeight: number, verticalFovRadians: number): number {
  if (radius <= 0) return 0
  if (Math.abs(depth) <= radius) return Number.POSITIVE_INFINITY
  if (depth < 0) return 0
  return 2 * radius * (viewportHeight / (2 * Math.tan(verticalFovRadians / 2))) / depth
}

export function selectLod(previous: LodLevel, pixels: number, inView: boolean): LodLevel {
  if (!inView) return 'culled'

  const promotes = (threshold: number): boolean => pixels >= threshold * (1 + HYSTERESIS)
  const retains = (threshold: number): boolean => pixels >= threshold * (1 - HYSTERESIS)

  if (previous === 'full' && retains(BANDS.full)) return 'full'
  if (previous === 'reduced' && retains(BANDS.reduced)) {
    if (promotes(BANDS.full)) return 'full'
    return 'reduced'
  }
  if (previous === 'marker' && retains(BANDS.marker)) {
    if (promotes(BANDS.full)) return 'full'
    if (promotes(BANDS.reduced)) return 'reduced'
    return 'marker'
  }
  if (previous === 'culled') {
    if (promotes(BANDS.full)) return 'full'
    if (promotes(BANDS.reduced)) return 'reduced'
    if (promotes(BANDS.marker)) return 'marker'
    return 'culled'
  }

  if (promotes(BANDS.full)) return 'full'
  if (retains(BANDS.reduced)) return 'reduced'
  return retains(BANDS.marker) ? 'marker' : 'culled'
}
