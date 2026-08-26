import { describe, expect, it } from 'vitest'
import { projectedDiameterPx, selectLod } from '../../orchard/lod-policy'

describe('projected tree LOD', () => {
  it('uses projected size rather than raw distance', () => {
    expect(projectedDiameterPx(10, 100, 1000, Math.PI / 2)).toBeCloseTo(100)
    expect(projectedDiameterPx(10, 100, 2000, Math.PI / 2)).toBeCloseTo(200)
  })

  it('treats positive bounds intersecting the camera plane as effectively infinite', () => {
    expect(projectedDiameterPx(10, 10, 1000, Math.PI / 2)).toBe(Number.POSITIVE_INFINITY)
    expect(projectedDiameterPx(10, -4, 1000, Math.PI / 2)).toBe(Number.POSITIVE_INFINITY)
    expect(projectedDiameterPx(10, -11, 1000, Math.PI / 2)).toBe(0)
    expect(projectedDiameterPx(0, -4, 1000, Math.PI / 2)).toBe(0)
  })

  it('selects fixed bands with hysteresis', () => {
    expect(selectLod('culled', 3, true)).toBe('marker')
    expect(selectLod('marker', 21, true)).toBe('marker')
    expect(selectLod('marker', 24, true)).toBe('reduced')
    expect(selectLod('full', 120, true)).toBe('full')
    expect(selectLod('full', 118, true)).toBe('reduced')
    expect(selectLod('full', 500, false)).toBe('culled')
  })

  it('promotes a culled tree to marker only at the outer marker threshold', () => {
    expect(selectLod('culled', 2.29, true)).toBe('culled')
    expect(selectLod('culled', 2.3, true)).toBe('marker')
  })

  it('retains a marker through the inner marker threshold', () => {
    expect(selectLod('marker', 1.69, true)).toBe('culled')
    expect(selectLod('marker', 1.7, true)).toBe('marker')
  })

  it('promotes a marker to reduced only at the outer reduced threshold', () => {
    expect(selectLod('marker', 22.99, true)).toBe('marker')
    expect(selectLod('marker', 23, true)).toBe('reduced')
  })

  it('retains reduced through the inner reduced threshold', () => {
    expect(selectLod('reduced', 16.99, true)).toBe('marker')
    expect(selectLod('reduced', 17, true)).toBe('reduced')
  })

  it('promotes reduced to full only at the outer full threshold', () => {
    expect(selectLod('reduced', 160.99, true)).toBe('reduced')
    expect(selectLod('reduced', 161, true)).toBe('full')
  })

  it('retains full through the inner full threshold', () => {
    expect(selectLod('full', 118.99, true)).toBe('reduced')
    expect(selectLod('full', 119, true)).toBe('full')
  })

  it('always culls an out-of-view tree', () => {
    expect(selectLod('full', 1000, false)).toBe('culled')
    expect(selectLod('culled', 1000, false)).toBe('culled')
  })
})
