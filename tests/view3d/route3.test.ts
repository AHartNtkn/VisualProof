import { describe, expect, it } from 'vitest'
import { routeAll, clearPoint, type Capsule, type NetIn } from '../../src/view3d/route3'
import { dist3, norm3, segPointDist, segSegDist, sub3, v3, type Vec3 } from '../../src/view3d/vec3'

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
    const routed = routeAll([{ id: 'w0', edges: [{ p, q, tp: null, tq: null }], exempt: [] }], trunk, DELTA)
    const pts = routed.get('w0')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(dist3(pts[pts.length - 1]!, q)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('a second nearby wire clears both the trunk and the first wire', () => {
    // Anchors are per-net exempt only (I7): a later wire gets no exemption
    // near an earlier wire's anchors, so the fixture keeps the two wires'
    // own anchors ≥ δ apart from EACH OTHER (0.6 here) — anything closer
    // would make the anchors themselves mutually unroutable by construction,
    // independent of any router capability.
    const mk = (y: number): NetIn => ({
      id: `w${y}`,
      edges: [{ p: v3(-2, y, 0), q: v3(2, y, 0), tp: null, tq: null }],
      exempt: [v3(-2, y, 0), v3(2, y, 0)],
    })
    const anchors = [v3(-2, 3, 0), v3(2, 3, 0), v3(-2, 3.6, 0), v3(2, 3.6, 0)]
    const routed = routeAll([mk(3), mk(3.6)], trunk, DELTA)
    const first = routed.get('w3')![0]!
    const second = routed.get('w3.6')![0]!
    const firstCaps: Capsule[] = first.slice(1).map((b, i) => ({ a: first[i]!, b, r: 0 }))
    expect(minDistToCaps(second, trunk, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
    expect(minDistToCaps(second, firstCaps, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('an anchored wire may hug the tree inside its exemption ball, not outside', () => {
    const anchor = v3(0, 3, 0) // ON the trunk
    const routed = routeAll(
      [{ id: 'wa', edges: [{ p: anchor, q: v3(3, 3, 0), tp: v3(1, 0, 0), tq: null }], exempt: [anchor] }],
      trunk, DELTA,
    )
    const pts = routed.get('wa')![0]!
    expect(minDistToCaps(pts, trunk, [anchor])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('respects a start tangent', () => {
    const p = v3(2, 0, 0), q = v3(2, 6, 0)
    const routed = routeAll([{ id: 'wt', edges: [{ p, q, tp: v3(1, 0, 0), tq: null }], exempt: [] }], [], DELTA)
    const pts = routed.get('wt')![0]!
    const d0 = norm3(sub3(pts[1]!, pts[0]!))
    expect(d0.x).toBeGreaterThan(0.7) // leaves along +x before bending toward q
  })
  it('is deterministic', () => {
    const nets: NetIn[] = [{ id: 'w', edges: [{ p: v3(-2, 3, 0), q: v3(2, 3.05, 0.02), tp: null, tq: null }], exempt: [] }]
    expect(routeAll(nets, trunk, DELTA)).toEqual(routeAll(nets, trunk, DELTA))
  })
  it('penetrations next to a fixed endpoint are caught and repaired', () => {
    const p = v3(0.31, 3, 0), q = v3(3, 3, 0)
    const routed = routeAll([{ id: 'we', edges: [{ p, q, tp: v3(-1, 0, 0), tq: null }], exempt: [] }], trunk, DELTA)
    const pts = routed.get('we')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('a multi-edge NetIn whose edges share a junction routes within-net without crossing itself', () => {
    // A Y-shaped net: three terminals meeting at a shared junction vertex,
    // expressed as three edges from each terminal to the same junction point.
    const junction = v3(0, 5, 0)
    const t0 = v3(-3, 2, 0), t1 = v3(3, 2, 0), t2 = v3(0, 9, 2)
    const net: NetIn = {
      id: 'wy',
      edges: [
        { p: t0, q: junction, tp: null, tq: null },
        { p: t1, q: junction, tp: null, tq: null },
        { p: t2, q: junction, tp: null, tq: null },
      ],
      exempt: [t0, t1, t2, junction],
    }
    const routed = routeAll([net], trunk, DELTA)
    const curves = routed.get('wy')!
    expect(curves.length).toBe(3)
    // Every edge starts at its declared terminal and ends at the junction.
    const terminals = [t0, t1, t2]
    curves.forEach((pts, i) => {
      expect(dist3(pts[0]!, terminals[i]!)).toBeLessThan(1e-9)
      expect(dist3(pts[pts.length - 1]!, junction)).toBeLessThan(1e-9)
    })
    // Every edge clears the trunk outside its own exemption ball.
    for (const pts of curves) expect(minDistToCaps(pts, trunk, net.exempt)).toBeGreaterThanOrEqual(DELTA * 0.999)
    // The three edges of the SAME net don't cross each other's bodies away
    // from the shared junction (each is a legitimate obstacle to the others
    // once routed, and later edges must clear earlier ones of the same net).
    for (let i = 0; i < curves.length; i++) for (let j = i + 1; j < curves.length; j++) {
      const a = curves[i]!, b = curves[j]!
      for (let k = 0; k < a.length - 1; k++) {
        if (net.exempt.some((e) => dist3(a[k]!, e) < 2.5 * DELTA) || net.exempt.some((e) => dist3(a[k + 1]!, e) < 2.5 * DELTA)) continue
        for (let m = 0; m < b.length - 1; m++) {
          if (net.exempt.some((e) => dist3(b[m]!, e) < 2.5 * DELTA) || net.exempt.some((e) => dist3(b[m + 1]!, e) < 2.5 * DELTA)) continue
          expect(segSegDist(a[k]!, a[k + 1]!, b[m]!, b[m + 1]!)).toBeGreaterThanOrEqual(DELTA * 0.95)
        }
      }
    }
  })
  it('symmetric clearance: several near-parallel chords through the trunk stay ≥ δ apart, edges vs samples in BOTH directions', () => {
    // A busy fixture of several near-parallel chords through the trunk,
    // forcing each new wire to detour around all previously routed ones.
    // Anchors are spaced ≥ δ apart (I7: exemption is per-net only, so
    // closer anchors would be mutually unroutable by construction — not a
    // router failure). Even with that spacing, once each wire detours
    // around the others its OWN samples can end up dense enough that an
    // edge (between two of a wire's own samples) passes closer to another
    // wire's polyline than either of its own sample points does — the
    // exact case point-vs-capsule scanning misses and edge-vs-capsule
    // scanning catches.
    const ys = [3.0, 3.6, 4.2, 4.8, 5.4, 6.0, 6.6]
    const nets: NetIn[] = ys.map((y, i) => {
      const p = v3(-2, y, 0.02 * i), q = v3(2, y - 0.03 * i, -0.02 * i)
      return { id: `wp${i}`, edges: [{ p, q, tp: null, tq: null }], exempt: [p, q] }
    })
    const routed = routeAll(nets, trunk, DELTA)
    const polylines = nets.map((n) => ({ id: n.id, exempt: n.exempt, pts: routed.get(n.id)![0]! }))

    const nearOwnAnchor = (wire: { exempt: Vec3[] }, p: Vec3): boolean =>
      wire.exempt.some((e) => dist3(p, e) < 2.5 * DELTA)

    let worst = Infinity
    for (let i = 0; i < polylines.length; i++) for (let j = 0; j < polylines.length; j++) {
      if (i === j) continue
      const wireA = polylines[i]!, wireB = polylines[j]!
      // wireA's EDGES vs wireB's SAMPLE POINTS (and, by swapping i/j across
      // the full double loop, the reverse direction too).
      for (let e = 0; e < wireA.pts.length - 1; e++) {
        const a0 = wireA.pts[e]!, a1 = wireA.pts[e + 1]!
        if (nearOwnAnchor(wireA, a0) && nearOwnAnchor(wireA, a1)) continue
        for (const b of wireB.pts) {
          if (nearOwnAnchor(wireB, b)) continue
          worst = Math.min(worst, segPointDist(b, a0, a1))
        }
      }
    }
    expect(worst).toBeGreaterThanOrEqual(DELTA * 0.95)
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
