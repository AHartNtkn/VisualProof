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
  it('uses the approved viewport-height lens and aperture-bound folio at 1600x1000', () => {
    const layout = interfaceLayout(1600, 1000)
    expect(layout.compact).toBe(false)
    expect(layout.folio.presentation).toBe('open')
    expect(layout.lens).toEqual({ left: 600, top: 0, size: 1000 })
    expect(layout.folio.width).toBeCloseTo(Math.min(736.2, 628.8), 0)
  })

  it('uses the approved viewport-height lens at 1920x1080', () => {
    const layout = interfaceLayout(1920, 1080)
    expect(layout.compact).toBe(false)
    expect(layout.lens).toEqual({ left: 840, top: 0, size: 1080 })
  })

  it('does not let desktop folio allocation alter lens size', () => {
    const narrower = interfaceLayout(1600, 1000)
    const wider = interfaceLayout(2000, 1000)
    expect(narrower.folio.width).not.toBe(wider.folio.width)
    expect(narrower.lens.size).toBe(1000)
    expect(wider.lens.size).toBe(1000)
  })

  it('retracts the folio to a left-edge drawer and keeps the narrow lens centered', () => {
    const layout = interfaceLayout(760, 900)
    expect(layout.compact).toBe(true)
    expect(layout.folio.presentation).toBe('drawer')
    expect(layout.folio.visibleHandle).toBeGreaterThanOrEqual(44)
    expect(layout.folio.left).toBeLessThan(0)
    expect(layout.folio.left + layout.folio.width).toBe(layout.folio.visibleHandle)
    expect(layout.lens.left + layout.lens.size / 2).toBeCloseTo(380)
    expect(layout.lens.left).toBeGreaterThanOrEqual(16)
    expect(layout.lens.left + layout.lens.size).toBeLessThanOrEqual(744)
  })
})
