import { describe, expect, it } from 'vitest'
import {
  clampSheetScroll,
  folioScrollForCulture,
  interfaceLayout,
} from '../../src/game/interface/folio-layout'
import { cultureId } from '../../src/game/types'

describe('continuous excavation sheet geometry', () => {
  it('clamps native scroll to actual long-sheet bounds', () => {
    expect(clampSheetScroll(-20, 2400, 720)).toBe(0)
    expect(clampSheetScroll(460, 2400, 720)).toBe(460)
    expect(clampSheetScroll(5000, 2400, 720)).toBe(1680)
    expect(clampSheetScroll(200, 600, 720)).toBe(0)
  })

  it('restores and clamps each culture independently', () => {
    const first = cultureId('first-culture')
    const second = cultureId('second-culture')
    const scrolls = new Map([[first, 900], [second, 120]])
    expect(folioScrollForCulture(scrolls, first, 1300, 500)).toBe(800)
    expect(folioScrollForCulture(scrolls, second, 1300, 500)).toBe(120)
  })
})

describe('production lens and folio layout', () => {
  it('uses a full-height lens centered in the stage remaining beside the open folio', () => {
    const layout = interfaceLayout(1600, 1000)
    expect(layout.compact).toBe(false)
    expect(layout.folio.presentation).toBe('open')
    expect(layout.lens.size).toBe(968)
    expect(layout.lens.top).toBe(16)
    const remainingCenter = layout.folio.width + (1600 - layout.folio.width) / 2
    expect(layout.lens.left + layout.lens.size / 2).toBeCloseTo(remainingCenter)
  })

  it('retracts the folio to a left-edge drawer and keeps the narrow lens centered', () => {
    const layout = interfaceLayout(760, 900)
    expect(layout.compact).toBe(true)
    expect(layout.folio.presentation).toBe('drawer')
    expect(layout.folio.visibleHandle).toBeGreaterThanOrEqual(44)
    expect(layout.folio.left).toBeLessThan(0)
    expect(layout.lens.left + layout.lens.size / 2).toBeCloseTo(380)
    expect(layout.lens.left).toBeGreaterThanOrEqual(16)
    expect(layout.lens.left + layout.lens.size).toBeLessThanOrEqual(744)
  })
})
