import { describe, expect, it } from 'vitest'
import {
  FOV_DEG, eyeOf, escapesFraming, fitPose, orbited, panned, zoomed,
} from '../../src/view3d/camera'
import { dist3, dot3, norm3, sub3, v3 } from '../../src/view3d/vec3'

const HALF_FOV = (FOV_DEG * Math.PI) / 360

describe('camera pose', () => {
  it('fitPose frames the bounding sphere inside the field of view', () => {
    const p = fitPose(v3(1, 2, 3), 5)
    expect(p.target).toEqual(v3(1, 2, 3))
    expect(Math.asin(5 / p.dist)).toBeLessThanOrEqual(HALF_FOV)
  })
  it('eyeOf sits at dist from target', () => {
    const p = fitPose(v3(0, 0, 0), 2)
    expect(dist3(eyeOf(p), p.target)).toBeCloseTo(p.dist, 9)
  })
  it('orbit accumulates yaw and clamps pitch', () => {
    let p = fitPose(v3(0, 0, 0), 2)
    const yaw0 = p.yaw
    p = orbited(p, 100, 0)
    expect(p.yaw).not.toBe(yaw0)
    p = orbited(p, 0, 1e6)
    expect(Math.abs(p.pitch)).toBeLessThanOrEqual(1.45)
  })
  it('zoom is multiplicative with a floor', () => {
    const p = fitPose(v3(0, 0, 0), 2)
    expect(zoomed(p, 100).dist).toBeGreaterThan(p.dist)
    expect(zoomed(p, -100).dist).toBeLessThan(p.dist)
    expect(zoomed(p, -1e9).dist).toBeGreaterThan(0)
  })
  it('pan moves the target perpendicular to the view direction', () => {
    const p = fitPose(v3(0, 0, 0), 2)
    const q = panned(p, 40, 25, 800)
    const view = norm3(sub3(p.target, eyeOf(p)))
    expect(Math.abs(dot3(sub3(q.target, p.target), view))).toBeLessThan(1e-9)
    expect(dist3(q.target, p.target)).toBeGreaterThan(0)
  })
  it('escapesFraming: false for the fitted bounds, true when the scene doubles', () => {
    const p = fitPose(v3(0, 0, 0), 2)
    expect(escapesFraming(p, v3(0, 0, 0), 2)).toBe(false)
    expect(escapesFraming(p, v3(0, 0, 0), 4)).toBe(true)
    expect(escapesFraming(p, v3(10, 0, 0), 2)).toBe(true)
  })
})
