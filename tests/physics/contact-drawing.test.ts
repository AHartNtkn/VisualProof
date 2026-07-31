import { describe, it, expect } from 'vitest'
import { mkFreeSpace, route, polylineTurning } from '../../src/view/route/freespace'
import type { HugArc } from '../../src/view/route/freespace'
import { edgeCurveCubics, edgeCurvePts } from '../../src/view/route/curve'
import type { Vec2 } from '../../src/view/vec'

/**
 * CONTACT-ANCHORED DRAWING (spec 2026-07-31): a wire detouring around an
 * obstacle circle is drawn as a Hobby chain anchored on the route's CONTACT
 * structure (one tangent-clamped anchor per quarter-turn of hug), never on
 * the route's sampled arc points. A spline through arc samples IS the arc —
 * the rejected "straight line connected to a circular arc" drafting look —
 * and the circumscribed sampling circle's radial jogs were the reported
 * zigzag notches. These tests pin the representation class, the turning
 * budget, the scale-invariance of the construction, continuity through first
 * contact, and the insensitivity of the drawn curve to the anchor-span bound.
 */

/** Two terminals on a line through a lone obstacle disc: the route must hug.
    Geometry is proportional to r, so the hug sweep (and everything but
    absolute size) is identical at every scale. */
function detour(r: number): { sweep: number; cubics: ReturnType<typeof edgeCurveCubics>; pts: Vec2[] } {
  const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r }], null)
  const p = { x: -1.25 * r, y: 0 }
  const q = { x: 1.25 * r, y: 0 }
  const rt = route(fs, p, q)
  expect(rt.hugs.length, 'the route hugs the disc').toBe(1)
  // symmetric bitangent hug: sweep = π − 2·acos(r/d)
  const sweep = Math.PI - 2 * Math.acos(r / (1.25 * r))
  return {
    sweep,
    cubics: edgeCurveCubics(null, null, p, q, rt.hugs),
    pts: edgeCurvePts(null, null, p, q, rt.hugs),
  }
}

/** Symmetric polyline Hausdorff distance (point-to-SEGMENT, so different
    sampling densities of the same curve measure ~0, not the sample spacing). */
const hausdorff = (a: readonly Vec2[], b: readonly Vec2[]): number => {
  const segDist = (p: Vec2, u: Vec2, v: Vec2): number => {
    const vx = v.x - u.x, vy = v.y - u.y
    const vv = vx * vx + vy * vy
    const t = vv < 1e-18 ? 0 : Math.max(0, Math.min(1, ((p.x - u.x) * vx + (p.y - u.y) * vy) / vv))
    return Math.hypot(u.x + vx * t - p.x, u.y + vy * t - p.y)
  }
  const side = (xs: readonly Vec2[], ys: readonly Vec2[]): number => {
    let worst = 0
    for (const x of xs) {
      let best = Infinity
      for (let i = 0; i + 1 < ys.length; i++) best = Math.min(best, segDist(x, ys[i]!, ys[i + 1]!))
      worst = Math.max(worst, best)
    }
    return worst
  }
  return Math.max(side(a, b), side(b, a))
}

describe('contact-anchored wire drawing', () => {
  it('a hug draws with quarter-turn contact anchors, not arc samples', () => {
    const { sweep, cubics } = detour(100)
    // anchors: hug entry + exit + ⌊sweep/(π/2)⌋ grid points, plus the two
    // terminals ⇒ pieces = anchors + 1
    const maxPieces = Math.floor(sweep / (Math.PI / 2)) + 4
    expect(
      cubics.length,
      `hug of sweep ${sweep.toFixed(2)} must draw ≤ ${maxPieces} Hobby pieces, got ${cubics.length} (arc-sample interpolation)`,
    ).toBeLessThanOrEqual(maxPieces)
  })

  it('the drawn turning stays within the hug sweep plus blending (no notches)', () => {
    const { sweep, pts } = detour(100)
    // The old radial jogs onto the circumscribed sampling circle each added a
    // pair of near-perpendicular turns (measured 10.53 rad total against a
    // 1.85 rad sweep); a smooth blended curve turns just past the geometric
    // sweep. 0.6 rad of headroom covers the Hobby entry/exit blend.
    const turn = polylineTurning(pts)
    expect(turn, `drawn turning ${turn.toFixed(2)} vs sweep ${sweep.toFixed(2)}`).toBeLessThanOrEqual(sweep + 0.6)
  })

  it('the construction class is scale-invariant (node-size and cut-size discs draw alike)', () => {
    const small = detour(7)
    const big = detour(100)
    expect(
      big.cubics.length,
      `same normalized geometry must draw the same piece count at every radius (r=7: ${small.cubics.length}, r=100: ${big.cubics.length})`,
    ).toBe(small.cubics.length)
  })

  it('the drawn curve is continuous through first contact with a disc', () => {
    // A straight wire grazed by a growing disc: at r slightly below the graze
    // radius the route is direct (no hugs); slightly above, a hug of sweep→0
    // appears. The two drawn curves must nearly coincide.
    const p = { x: -100, y: 0 }
    const q = { x: 100, y: 0 }
    const graze = 20 // disc center at (0, -20): contact begins at r = 20
    const eps = 0.05
    const below = route(mkFreeSpace([{ c: { x: 0, y: -graze }, r: graze - eps }], null), p, q)
    const above = route(mkFreeSpace([{ c: { x: 0, y: -graze }, r: graze + eps }], null), p, q)
    expect(below.hugs.length).toBe(0)
    expect(above.hugs.length).toBe(1)
    const a = edgeCurvePts(null, null, p, q, below.hugs)
    const b = edgeCurvePts(null, null, p, q, above.hugs)
    expect(hausdorff(a, b), 'first contact must not jump the drawn curve').toBeLessThan(1.5)
  })

  it('the drawn curve is insensitive to the anchor span bound (π/3 vs π/2 vs π)', () => {
    // Splitting a hug into k equal adjacent sub-arcs reproduces the anchor
    // sets of smaller span bounds through the same public API: the sub-arc
    // count plays the role of ⌈sweep/span⌉. All choices must draw the same
    // curve to visual tolerance — the claim that HUG_SPAN is a derived bound.
    const r = 100
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r }], null)
    const p = { x: -1.25 * r, y: 0 }
    const q = { x: 1.25 * r, y: 0 }
    const rt = route(fs, p, q)
    const h = rt.hugs[0]!
    const split = (k: number): HugArc[] =>
      Array.from({ length: k }, (_, i) => ({ c: h.c, r: h.r, from: h.from + (h.sweep * i) / k, sweep: h.sweep / k }))
    const one = edgeCurvePts(null, null, p, q, split(1))
    const two = edgeCurvePts(null, null, p, q, split(2))
    const three = edgeCurvePts(null, null, p, q, split(3))
    // measured 0.66 wu on r=100 (the Hobby piece's deviation from the arc at
    // a quarter-turn span) — sub-pixel at scene scale; 1.0 bounds it
    expect(hausdorff(one, two)).toBeLessThan(1.0)
    expect(hausdorff(one, three)).toBeLessThan(1.0)
  })
})
