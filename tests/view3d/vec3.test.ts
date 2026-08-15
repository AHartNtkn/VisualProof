import { describe, expect, it } from 'vitest'
import {
  v3, add3, sub3, scale3, dot3, cross3, len3, dist3, norm3, lerp3,
  anyPerp, rotateAbout, segClosest, segPointDist,
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
})
