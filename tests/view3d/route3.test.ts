import { describe, expect, it } from 'vitest'
import { routeAll, clearPoint, type Capsule } from '../../src/view3d/route3'
import { dist3, norm3, segPointDist, sub3, v3, type Vec3 } from '../../src/view3d/vec3'

const DELTA = 0.3
const trunk: Capsule[] = [{ a: v3(0, 0, 0), b: v3(0, 10, 0), r: 0 }]

const minDistToCaps = (pts: Vec3[], caps: Capsule[], exempt: Vec3[]): number => {
  let m = Infinity
  for (const p of pts) {
    if (exempt.some((e) => dist3(p, e) < 2.5 * DELTA)) continue
    for (const c of caps) m = Math.min(m, segPointDist(p, c.a, c.b) - c.r)
  }
  return m
}

describe('routeAll', () => {
  it('a wire whose chord pierces the trunk detours ≥ δ around it, endpoints fixed', () => {
    const p = v3(-2, 3, 0), q = v3(2, 3, 0)
    const routed = routeAll([{ id: 'w0', edges: [{ p, q, tp: null, tq: null }] }], trunk, [], DELTA)
    const pts = routed.get('w0')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(dist3(pts[pts.length - 1]!, q)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('a second nearby wire clears both the trunk and the first wire', () => {
    const mk = (y: number) => ({ id: `w${y}`, edges: [{ p: v3(-2, y, 0), q: v3(2, y, 0), tp: null, tq: null }] })
    const anchors = [v3(-2, 3, 0), v3(2, 3, 0), v3(-2, 3.1, 0), v3(2, 3.1, 0)]
    const routed = routeAll([mk(3), mk(3.1)], trunk, anchors, DELTA)
    const first = routed.get('w3')![0]!
    const second = routed.get('w3.1')![0]!
    const firstCaps: Capsule[] = first.slice(1).map((b, i) => ({ a: first[i]!, b, r: 0 }))
    expect(minDistToCaps(second, trunk, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
    expect(minDistToCaps(second, firstCaps, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('an anchored wire may hug the tree inside its exemption ball, not outside', () => {
    const anchor = v3(0, 3, 0) // ON the trunk
    const routed = routeAll(
      [{ id: 'wa', edges: [{ p: anchor, q: v3(3, 3, 0), tp: v3(1, 0, 0), tq: null }] }],
      trunk, [anchor], DELTA,
    )
    const pts = routed.get('wa')![0]!
    expect(minDistToCaps(pts, trunk, [anchor])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('respects a start tangent', () => {
    const p = v3(2, 0, 0), q = v3(2, 6, 0)
    const routed = routeAll([{ id: 'wt', edges: [{ p, q, tp: v3(1, 0, 0), tq: null }] }], [], [], DELTA)
    const pts = routed.get('wt')![0]!
    const d0 = norm3(sub3(pts[1]!, pts[0]!))
    expect(d0.x).toBeGreaterThan(0.7) // leaves along +x before bending toward q
  })
  it('is deterministic', () => {
    const nets = [{ id: 'w', edges: [{ p: v3(-2, 3, 0), q: v3(2, 3.05, 0.02), tp: null, tq: null }] }]
    expect(routeAll(nets, trunk, [], DELTA)).toEqual(routeAll(nets, trunk, [], DELTA))
  })
  it('penetrations next to a fixed endpoint are caught and repaired', () => {
    const p = v3(0.31, 3, 0), q = v3(3, 3, 0)
    const routed = routeAll([{ id: 'we', edges: [{ p, q, tp: v3(-1, 0, 0), tq: null }] }], trunk, [], DELTA)
    const pts = routed.get('we')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
})

describe('clearPoint', () => {
  it('pushes an embedded point out to δ clearance deterministically', () => {
    const p = v3(0.01, 5, 0)
    const out = clearPoint(p, trunk, [], DELTA)
    expect(segPointDist(out, trunk[0]!.a, trunk[0]!.b)).toBeGreaterThanOrEqual(DELTA * 0.999)
    expect(clearPoint(p, trunk, [], DELTA)).toEqual(out)
  })
})
