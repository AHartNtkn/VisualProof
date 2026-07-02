import { describe, it, expect } from 'vitest'
import { fitCamera, DESIGN_SCALE } from '../../src/view/camera'

/**
 * The camera fit must always yield a POSITIVE FINITE scale: the shell's toWorld
 * divides pointer coordinates by view.scale, so a 0/negative/NaN scale poisons
 * the whole frame's pointer→world mapping. These cases cover the reachable
 * frames (which compute a real fit) and the degenerate ones the guard exists
 * for (empty diagram, R fallback, zero/NaN viewport).
 */
describe('fitCamera — scale is always positive and finite', () => {
  const sheet = (radius: number, cx = 0, cy = 0) => ({ center: { x: cx, y: cy }, radius })

  it('normal viewport caps at the design unit scale and centers on the sheet', () => {
    const cam = fitCamera(sheet(10, 3, -4), 800, 600, 1)
    // (0.45 * 600) / 10 = 27, capped at DESIGN_SCALE
    expect(cam.scale).toBe(DESIGN_SCALE)
    expect(cam.offsetX).toBe(800 / 2 - 3 * DESIGN_SCALE)
    expect(cam.offsetY).toBe(600 / 2 - -4 * DESIGN_SCALE)
  })

  it('a small viewport scales the sheet down (below the cap), still positive', () => {
    const cam = fitCamera(sheet(10), 100, 100, 1)
    expect(cam.scale).toBeCloseTo((0.45 * 100) / 10, 10) // 4.5
    expect(cam.scale).toBeGreaterThan(0)
  })

  it('an empty diagram (no sheet region) uses the R=10 floor, not a zero scale', () => {
    const cam = fitCamera(undefined, 800, 600, 1)
    expect(Number.isFinite(cam.scale)).toBe(true)
    expect(cam.scale).toBeGreaterThan(0)
    expect(cam.offsetX).toBe(400)
    expect(cam.offsetY).toBe(300)
  })

  it('userZoom scales the fit and stays positive at extreme zoom-out', () => {
    const inn = fitCamera(sheet(10), 800, 600, 3)
    const out = fitCamera(sheet(10), 800, 600, 1e-6)
    expect(inn.scale).toBeGreaterThan(out.scale)
    expect(out.scale).toBeGreaterThan(0)
  })

  it('a degenerate zero-extent viewport falls back to a positive finite scale', () => {
    const cam = fitCamera(sheet(10), 0, 0, 1)
    // raw = min(6, 0/10) * 1 = 0 → guarded to the design unit scale
    expect(cam.scale).toBe(DESIGN_SCALE)
    expect(Number.isFinite(cam.offsetX) && Number.isFinite(cam.offsetY)).toBe(true)
  })

  it('a non-finite sheet radius falls back to a positive finite scale', () => {
    const cam = fitCamera(sheet(NaN), 800, 600, 1)
    expect(Number.isFinite(cam.scale)).toBe(true)
    expect(cam.scale).toBeGreaterThan(0)
  })

  it('a huge sheet against a normal viewport still yields a positive scale', () => {
    const cam = fitCamera(sheet(1e6), 800, 600, 1)
    expect(cam.scale).toBeGreaterThan(0)
    expect(Number.isFinite(cam.scale)).toBe(true)
  })
})
