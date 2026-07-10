import { describe, expect, it } from 'vitest'
import { fitCamera } from '../../src/view/camera'

const sheet = (radius: number, x = 0, y = 0) => ({ center: { x, y }, radius })
const screenCenter = (
  camera: ReturnType<typeof fitCamera>,
  center: { readonly x: number; readonly y: number },
) => ({
  x: center.x * camera.scale + camera.offsetX,
  y: center.y * camera.scale + camera.offsetY,
})

describe('fitCamera — canonical frame fit', () => {
  it.each([4, 10, 75, 1_000])(
    'fits a stored frame of radius %s to 90%% of the smaller viewport extent',
    (radius) => {
      const camera = fitCamera(sheet(radius), 1_000, 600, 1)
      expect(2 * radius * camera.scale).toBeCloseTo(0.9 * 600, 10)
    },
  )

  it('centers the stored frame rather than the world origin', () => {
    const frame = sheet(35, 120, -80)
    const camera = fitCamera(frame, 900, 500, 1)
    expect(screenCenter(camera, frame.center)).toEqual({ x: 450, y: 250 })
  })

  it('refits the same frame to the same viewport fraction after resize', () => {
    const frame = sheet(20, 5, 7)
    const landscape = fitCamera(frame, 1_200, 800, 1)
    const portrait = fitCamera(frame, 500, 900, 1)

    expect(2 * frame.radius * landscape.scale).toBeCloseTo(720, 10)
    expect(2 * frame.radius * portrait.scale).toBeCloseTo(450, 10)
    expect(screenCenter(landscape, frame.center)).toEqual({ x: 600, y: 400 })
    expect(screenCenter(portrait, frame.center)).toEqual({ x: 250, y: 450 })
  })

  it('treats every sub-1 user zoom as the canonical full-frame fit', () => {
    const fullFit = fitCamera(sheet(30), 800, 600, 1)
    expect(fitCamera(sheet(30), 800, 600, 0.1)).toEqual(fullFit)
    expect(fitCamera(sheet(30), 800, 600, -5)).toEqual(fullFit)
  })

  it('caps user zoom at 8', () => {
    const maximum = fitCamera(sheet(30), 800, 600, 8)
    expect(fitCamera(sheet(30), 800, 600, 80)).toEqual(maximum)
    expect(maximum.scale).toBeCloseTo(fitCamera(sheet(30), 800, 600, 1).scale * 8, 10)
  })

  it.each([
    ['missing frame', undefined, 800, 600, 1],
    ['zero radius', sheet(0), 800, 600, 1],
    ['non-finite radius', sheet(Number.NaN), 800, 600, 1],
    ['zero viewport', sheet(10), 0, 0, 1],
    ['non-finite viewport', sheet(10), Number.NaN, Number.POSITIVE_INFINITY, 1],
    ['non-finite user zoom', sheet(10), 800, 600, Number.NaN],
  ] as const)('keeps camera geometry finite for a degenerate %s', (_name, frame, width, height, zoom) => {
    const camera = fitCamera(frame, width, height, zoom)
    expect(Number.isFinite(camera.scale)).toBe(true)
    expect(camera.scale).toBeGreaterThan(0)
    expect(Number.isFinite(camera.offsetX)).toBe(true)
    expect(Number.isFinite(camera.offsetY)).toBe(true)
  })
})
