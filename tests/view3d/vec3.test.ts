import { describe, expect, it } from 'vitest'
import {
  v3, add3, sub3, scale3, dot3, cross3, len3, dist3, norm3, lerp3,
  anyPerp, rotateAbout, segClosest, segPointDist, segSegDist,
} from '../../src/view3d/vec3'

describe('vec3', () => {
  it('basic algebra', () => {
    expect(add3(v3(1, 2, 3), v3(4, 5, 6))).toEqual(v3(5, 7, 9))
    expect(sub3(v3(4, 5, 6), v3(1, 2, 3))).toEqual(v3(3, 3, 3))
    expect(scale3(v3(1, -2, 3), 2)).toEqual(v3(2, -4, 6))
    expect(dot3(v3(1, 0, 0), v3(0, 1, 0))).toBe(0)
    expect(cross3(v3(1, 0, 0), v3(0, 1, 0))).toEqual(v3(0, 0, 1))
    expect(len3(v3(3, 4, 0))).toBe(5)
    expect(dist3(v3(1, 1, 1), v3(1, 1, 3))).toBe(2)
    expect(lerp3(v3(0, 0, 0), v3(2, 4, 6), 0.5)).toEqual(v3(1, 2, 3))
  })
  it('norm3 normalizes and throws on zero', () => {
    expect(len3(norm3(v3(0, 5, 0)))).toBeCloseTo(1, 12)
    expect(() => norm3(v3(0, 0, 0))).toThrow()
  })
  it('anyPerp is unit and perpendicular for the axes and a skew vector', () => {
    for (const u of [v3(1, 0, 0), v3(0, 1, 0), v3(0, 0, 1), norm3(v3(1, 2, 3))]) {
      const p = anyPerp(u)
      expect(len3(p)).toBeCloseTo(1, 12)
      expect(Math.abs(dot3(p, u))).toBeLessThan(1e-12)
    }
  })
  it('rotateAbout rotates x to y about z by 90 degrees', () => {
    const r = rotateAbout(v3(1, 0, 0), v3(0, 0, 1), Math.PI / 2)
    expect(r.x).toBeCloseTo(0, 12)
    expect(r.y).toBeCloseTo(1, 12)
    expect(r.z).toBeCloseTo(0, 12)
  })
  it('segment distance: interior projection and endpoint clamp', () => {
    const a = v3(0, 0, 0), b = v3(10, 0, 0)
    expect(segPointDist(v3(5, 3, 0), a, b)).toBeCloseTo(3, 12)
    expect(segClosest(v3(5, 3, 0), a, b)).toEqual(v3(5, 0, 0))
    expect(segPointDist(v3(-4, 3, 0), a, b)).toBeCloseTo(5, 12)
    expect(segPointDist(v3(2, 0, 0), a, a)).toBeCloseTo(2, 12) // degenerate segment
  })
  it('segSegDist: parallel, crossing, skew, and degenerate-point segments', () => {
    // Parallel segments offset by 3 on y: closest approach is the perpendicular gap.
    expect(segSegDist(v3(0, 0, 0), v3(10, 0, 0), v3(0, 3, 0), v3(10, 3, 0))).toBeCloseTo(3, 9)
    // Crossing segments (in-plane, forming an X): distance is 0.
    expect(segSegDist(v3(-1, -1, 0), v3(1, 1, 0), v3(-1, 1, 0), v3(1, -1, 0))).toBeCloseTo(0, 9)
    // Skew segments (classic case: along x at z=0, along y at z=1, both through origin-ish):
    // closest approach is the common perpendicular, length 1.
    expect(segSegDist(v3(-5, 0, 0), v3(5, 0, 0), v3(0, -5, 1), v3(0, 5, 1))).toBeCloseTo(1, 9)
    // Both segments degenerate to points.
    expect(segSegDist(v3(1, 2, 3), v3(1, 2, 3), v3(4, 6, 3), v3(4, 6, 3))).toBeCloseTo(5, 9)
    // One segment degenerate to a point, the other a real segment (point-to-segment).
    expect(segSegDist(v3(5, 3, 0), v3(5, 3, 0), v3(0, 0, 0), v3(10, 0, 0))).toBeCloseTo(3, 9)
    // Non-crossing finite segments whose infinite-line closest points fall
    // outside both segments: distance is between the nearest endpoints.
    expect(segSegDist(v3(0, 0, 0), v3(1, 0, 0), v3(3, 1, 0), v3(4, 1, 0))).toBeCloseTo(Math.hypot(2, 1), 9)
    // Symmetric: order of the two segments must not matter.
    const a1 = v3(-2, 3, 0), a2 = v3(2, 3.1, 0.5), b1 = v3(-1, 3.2, -0.3), b2 = v3(1, 2.9, 0.1)
    expect(segSegDist(a1, a2, b1, b2)).toBeCloseTo(segSegDist(b1, b2, a1, a2), 9)
  })
})
