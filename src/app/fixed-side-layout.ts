export type FixedSide = 'forward' | 'backward'

export type PaneRect = {
  readonly x: number
  readonly y: number
  readonly width: number
  readonly height: number
}

export type FixedSideGeometry = {
  readonly forward: PaneRect
  readonly seam: PaneRect
  readonly backward: PaneRect
}

export const FIXED_SIDE_SEAM_WIDTH = 8
export const MIN_FIXED_PANE_WIDTH = 320
export const MIN_FIXED_WORKSPACE_WIDTH = MIN_FIXED_PANE_WIDTH * 2 + FIXED_SIDE_SEAM_WIDTH

export function clampDividerRatio(ratio: number): number {
  return Math.max(0.3, Math.min(0.7, ratio))
}

export function dividerRatioAt(clientX: number, left: number, width: number): number {
  if (width <= 0) return 0.5
  return clampDividerRatio((clientX - left) / width)
}

export function paneGeometry(
  width: number,
  height: number,
  ratio: number,
  seamWidth = FIXED_SIDE_SEAM_WIDTH,
): FixedSideGeometry {
  const usable = Math.max(0, width - seamWidth)
  const forwardWidth = usable * clampDividerRatio(ratio)
  const backwardX = forwardWidth + seamWidth
  return {
    forward: { x: 0, y: 0, width: forwardWidth, height },
    seam: { x: forwardWidth, y: 0, width: seamWidth, height },
    backward: { x: backwardX, y: 0, width: usable - forwardWidth, height },
  }
}

export function otherSide(side: FixedSide): FixedSide {
  return side === 'forward' ? 'backward' : 'forward'
}
