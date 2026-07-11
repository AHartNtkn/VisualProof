import { describe, expect, it } from 'vitest'
import {
  MIN_FIXED_WORKSPACE_WIDTH,
  clampDividerRatio,
  dividerRatioAt,
  otherSide,
  paneGeometry,
} from '../../src/app/fixed-side-layout'

describe('fixed-side workspace geometry', () => {
  it('clamps every ratio to the approved 30–70 percent range', () => {
    expect(clampDividerRatio(-1)).toBe(0.3)
    expect(clampDividerRatio(0.42)).toBe(0.42)
    expect(clampDividerRatio(2)).toBe(0.7)
  })

  it('maps pointer position into the same clamped ratio', () => {
    expect(dividerRatioAt(50, 100, 1000)).toBe(0.3)
    expect(dividerRatioAt(600, 100, 1000)).toBe(0.5)
    expect(dividerRatioAt(1050, 100, 1000)).toBe(0.7)
  })

  it('allocates both panes around one seam without losing width', () => {
    const geometry = paneGeometry(1000, 700, 0.5, 8)
    expect(geometry).toEqual({
      forward: { x: 0, y: 0, width: 496, height: 700 },
      seam: { x: 496, y: 0, width: 8, height: 700 },
      backward: { x: 504, y: 0, width: 496, height: 700 },
    })
    expect(geometry.backward.x + geometry.backward.width).toBe(1000)
  })

  it('defines the minimum as two usable panes plus the seam', () => {
    expect(MIN_FIXED_WORKSPACE_WIDTH).toBe(648)
    expect(MIN_FIXED_WORKSPACE_WIDTH - 1).toBeLessThan(2 * 320 + 8)
  })

  it('switches front identity without inventing another state', () => {
    expect(otherSide('forward')).toBe('backward')
    expect(otherSide('backward')).toBe('forward')
  })
})
