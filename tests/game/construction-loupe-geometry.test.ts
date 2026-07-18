import { describe, expect, it } from 'vitest'
import {
  LOUPE_MAX_DIAMETER,
  LOUPE_MIN_DIAMETER,
  beginLoupeResize,
  clientToLoupeDraft,
  hitConstructionLoupe,
  loupeApertureRect,
  loupeRimHitWidth,
  loupeTerminalPoint,
  loupeTerminalRadius,
  moveConstructionLoupe,
  placeConstructionLoupe,
  resizeConstructionLoupe,
  type LoupeGeometry,
} from '../../src/game/interface/construction-loupe-geometry'

const viewport = { width: 1440, height: 900 }

const expectReachable = (geometry: LoupeGeometry, size = viewport): void => {
  const aperture = loupeApertureRect(geometry)
  const rimWidth = loupeRimHitWidth(geometry.diameter)
  const terminal = loupeTerminalPoint(geometry)
  const terminalRadius = loupeTerminalRadius(geometry.diameter)
  expect(aperture.left - rimWidth).toBeGreaterThanOrEqual(0)
  expect(aperture.top - rimWidth).toBeGreaterThanOrEqual(0)
  expect(aperture.left + aperture.width + rimWidth).toBeLessThanOrEqual(size.width)
  expect(aperture.top + aperture.height + rimWidth).toBeLessThanOrEqual(size.height)
  expect(terminal.x - terminalRadius).toBeGreaterThanOrEqual(0)
  expect(terminal.y - terminalRadius).toBeGreaterThanOrEqual(0)
  expect(terminal.x + terminalRadius).toBeLessThanOrEqual(size.width)
  expect(terminal.y + terminalRadius).toBeLessThanOrEqual(size.height)
}

describe('circular construction loupe geometry', () => {
  it('owns one center and one proportional diameter', () => {
    const geometry = placeConstructionLoupe({ x: 420, y: 240 }, viewport)
    expect(Object.keys(geometry).sort()).toEqual(['center', 'diameter'])
    expect(geometry.diameter).toBeGreaterThanOrEqual(LOUPE_MIN_DIAMETER)
    expect(geometry.diameter).toBeLessThanOrEqual(LOUPE_MAX_DIAMETER)
    expect(loupeApertureRect(geometry)).toMatchObject({
      width: geometry.diameter,
      height: geometry.diameter,
    })
    expectReachable(geometry)
  })

  it('clamps invocation placement, movement, and the terminal at every edge', () => {
    for (const invocation of [
      { x: -1000, y: -1000 },
      { x: 5000, y: -1000 },
      { x: -1000, y: 5000 },
      { x: 5000, y: 5000 },
    ]) expectReachable(placeConstructionLoupe(invocation, viewport))

    const initial = placeConstructionLoupe({ x: 600, y: 400 }, viewport)
    for (const delta of [
      { x: -5000, y: -5000 }, { x: 5000, y: -5000 },
      { x: -5000, y: 5000 }, { x: 5000, y: 5000 },
    ]) {
      const moved = moveConstructionLoupe(initial, delta, viewport)
      expect(moved.diameter).toBe(initial.diameter)
      expectReachable(moved)
    }
  })

  it('adapts to a small viewport without losing the rim or terminal', () => {
    const size = { width: 160, height: 150 }
    const geometry = placeConstructionLoupe({ x: 155, y: 145 }, size)
    expect(geometry.diameter).toBeLessThanOrEqual(LOUPE_MIN_DIAMETER)
    expectReachable(geometry, size)
  })

  it('resizes proportionally around the owned opposite anchor', () => {
    const initial = placeConstructionLoupe({ x: 500, y: 260 }, viewport, 360)
    const drag = beginLoupeResize(initial)
    const terminal = loupeTerminalPoint(initial)
    const grown = resizeConstructionLoupe(drag, { x: terminal.x + 120, y: terminal.y + 120 }, viewport)
    expect(grown.diameter).toBeGreaterThan(initial.diameter)
    expect(loupeApertureRect(grown).width).toBe(loupeApertureRect(grown).height)
    const nextDrag = beginLoupeResize(grown)
    expect(nextDrag.anchor.x).toBeCloseTo(drag.anchor.x, 6)
    expect(nextDrag.anchor.y).toBeCloseTo(drag.anchor.y, 6)
    expectReachable(grown)
  })

  it('hit-tests the semantic circle, rim, terminal, and outside separately', () => {
    const geometry = placeConstructionLoupe({ x: 500, y: 240 }, viewport, 400)
    const radius = geometry.diameter / 2
    expect(hitConstructionLoupe(geometry, geometry.center)).toBe('aperture')
    expect(hitConstructionLoupe(geometry, { x: geometry.center.x + radius - 3, y: geometry.center.y })).toBe('rim')
    expect(hitConstructionLoupe(geometry, loupeTerminalPoint(geometry))).toBe('terminal')
    expect(hitConstructionLoupe(geometry, { x: geometry.center.x - radius - 20, y: geometry.center.y })).toBe('outside')
  })

  it('maps client coordinates through the exact undistorted canvas rectangle', () => {
    const mapped = clientToLoupeDraft(
      { x: 250, y: 350 },
      { left: 100, top: 200, width: 300, height: 300 },
      { width: 900, height: 900 },
      { scale: 2, offsetX: 30, offsetY: 50 },
    )
    expect(mapped.screen).toEqual({ x: 450, y: 450 })
    expect(mapped.world).toEqual({ x: 210, y: 200 })
  })
})
