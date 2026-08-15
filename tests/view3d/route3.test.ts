import { describe, expect, it } from 'vitest'
import { routeAll, clearPoint, type Capsule, type NetIn } from '../../src/view3d/route3'
import { dist3, norm3, segPointDist, segSegClosest, segSegDist, sub3, v3, type Vec3 } from '../../src/view3d/vec3'

const DELTA = 0.3
const trunk: Capsule[] = [{ a: v3(0, 0, 0), b: v3(0, 10, 0), r: 0, g: 'reg:t' }]

/** A plain two-anchor net (no junctions). */
const straightNet = (id: string, p: Vec3, q: Vec3, tp: Vec3 | null = null, tq: Vec3 | null = null): NetIn =>
  ({ id, anchors: [p, q], tangents: [tp, tq], junctions: [], edges: [[0, 1]] })

const minDistToCaps = (pts: Vec3[], caps: Capsule[], exempt: Vec3[]): number => {
  let m = Infinity
  for (const p of pts) {
    if (exempt.some((e) => dist3(p, e) < 2.5 * DELTA)) continue
    for (const c of caps) m = Math.min(m, segPointDist(p, c.a, c.b) - c.r)
  }
  return m
}

describe('routeAll', () => {
  it('a sample inside an exemption ball still moves to clear a real hit', () => {
    // Exemption means ALLOWED to be close, never PINNED: an edge whose one
    // end sits just inside the anchor ball (0.60 from E) while its true
    // closest approach to the obstacle lies just outside (at 0.75+) is a
    // real violation, and the ball-side end must be free to move — pinning
    // it leaves the edge permanently 0.29 from the capsule, unclearable by
    // any motion of the other end alone.
    const E = v3(0, 0, 0)
    const C: Capsule = { a: v3(0.85, 0.15, 0), b: v3(1.05, 0.15, 0), r: 0, g: 'other' }
    const routed = routeAll([straightNet('wx', E, v3(3, 0, 0))], [C], DELTA)
    const pts = routed.get('wx')![0]!
    expect(dist3(pts[0]!, E)).toBeLessThan(1e-9)
    for (let i = 1; i < pts.length; i++) {
      const dEdge = segSegDist(pts[i - 1]!, pts[i]!, C.a, C.b)
      if (dEdge >= DELTA * 0.999) continue
      const [onEdge] = segSegClosest(pts[i - 1]!, pts[i]!, C.a, C.b)
      expect(dist3(onEdge, E)).toBeLessThan(2.5 * DELTA)
    }
  })
  it('a wire whose chord pierces the trunk detours ≥ δ around it, endpoints fixed', () => {
    const p = v3(-2, 3, 0), q = v3(2, 3, 0)
    const routed = routeAll([straightNet('w0', p, q)], trunk, DELTA)
    const pts = routed.get('w0')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(dist3(pts[pts.length - 1]!, q)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('routed curves are taut and rounded, not repair scribbles', () => {
    // Around a single line obstacle the shortest clear path is the chord
    // plus a small bulge: total length stays within a bulge's worth of the
    // direct chord, and no interior corner turns sharply. This is the
    // "distortion applied to a straight line" the design asks for — repair
    // history (spikes, zigzags, trunk-hugging wander) must not survive
    // into the output.
    const p = v3(-2, 3, 0), q = v3(2, 3, 0)
    const routed = routeAll([straightNet('w0', p, q)], trunk, DELTA)
    const pts = routed.get('w0')![0]!
    let length = 0
    for (let i = 1; i < pts.length; i++) length += dist3(pts[i - 1]!, pts[i]!)
    expect(length).toBeLessThanOrEqual(dist3(p, q) + 4 * DELTA)
    let maxTurn = 0
    for (let i = 1; i < pts.length - 1; i++) {
      const u = sub3(pts[i]!, pts[i - 1]!), w = sub3(pts[i + 1]!, pts[i]!)
      const lu = Math.hypot(u.x, u.y, u.z), lw = Math.hypot(w.x, w.y, w.z)
      if (lu < 1e-9 || lw < 1e-9) continue
      const cos = Math.min(1, Math.max(-1, (u.x * w.x + u.y * w.y + u.z * w.z) / (lu * lw)))
      maxTurn = Math.max(maxTurn, Math.acos(cos))
    }
    expect(maxTurn).toBeLessThanOrEqual(0.5)
  })
  it('a second nearby wire clears both the trunk and the first wire', () => {
    // Anchors are per-net exempt only (I7): a later wire gets no exemption
    // near an earlier wire's anchors, so the fixture keeps the two wires'
    // own anchors ≥ δ apart from EACH OTHER (0.6 here) — anything closer
    // would make the anchors themselves mutually unroutable by construction,
    // independent of any router capability.
    const mk = (y: number): NetIn => straightNet(`w${y}`, v3(-2, y, 0), v3(2, y, 0))
    const anchors = [v3(-2, 3, 0), v3(2, 3, 0), v3(-2, 3.6, 0), v3(2, 3.6, 0)]
    const routed = routeAll([mk(3), mk(3.6)], trunk, DELTA)
    const first = routed.get('w3')![0]!
    const second = routed.get('w3.6')![0]!
    const firstCaps: Capsule[] = first.slice(1).map((b, i) => ({ a: first[i]!, b, r: 0, g: 'w:w3' }))
    expect(minDistToCaps(second, trunk, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
    expect(minDistToCaps(second, firstCaps, anchors)).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('an anchored wire may hug the tree inside its exemption ball, not outside', () => {
    const anchor = v3(0, 3, 0) // ON the trunk
    const routed = routeAll([straightNet('wa', anchor, v3(3, 3, 0), v3(1, 0, 0))], trunk, DELTA)
    const pts = routed.get('wa')![0]!
    expect(minDistToCaps(pts, trunk, [anchor])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('respects a start tangent', () => {
    const p = v3(2, 0, 0), q = v3(2, 6, 0)
    const routed = routeAll([straightNet('wt', p, q, v3(1, 0, 0))], [], DELTA)
    const pts = routed.get('wt')![0]!
    const d0 = norm3(sub3(pts[1]!, pts[0]!))
    expect(d0.x).toBeGreaterThan(0.7) // leaves along +x before bending toward q
  })
  it('is deterministic', () => {
    const nets: NetIn[] = [straightNet('w', v3(-2, 3, 0), v3(2, 3.05, 0.02))]
    expect(routeAll(nets, trunk, DELTA)).toEqual(routeAll(nets, trunk, DELTA))
  })
  it('penetrations next to a fixed endpoint are caught and repaired', () => {
    // The start anchor sits 0.31 from the trunk — just OUTSIDE the licensed
    // meeting distance — so the tangent-into-the-trunk approach must be
    // repaired to full clearance everywhere.
    const p = v3(0.31, 3, 0), q = v3(3, 3, 0)
    const routed = routeAll([straightNet('we', p, q, v3(-1, 0, 0))], trunk, DELTA)
    const pts = routed.get('we')![0]!
    expect(dist3(pts[0]!, p)).toBeLessThan(1e-9)
    expect(minDistToCaps(pts, trunk, [])).toBeGreaterThanOrEqual(DELTA * 0.999)
  })
  it('a multi-edge NetIn whose edges share a junction routes within-net without crossing itself', () => {
    // A Y-shaped net: three terminals meeting at a shared junction vertex.
    const junction = v3(1.5, 5, 0)
    const t0 = v3(-3, 2, 0), t1 = v3(3, 2, 0), t2 = v3(0, 9, 2)
    const net: NetIn = {
      id: 'wy',
      anchors: [t0, t1, t2],
      tangents: [null, null, null],
      junctions: [junction],
      edges: [[0, 3], [1, 3], [2, 3]],
    }
    const exemptPts = [t0, t1, t2, junction]
    const routed = routeAll([net], trunk, DELTA)
    const curves = routed.get('wy')!
    expect(curves.length).toBe(3)
    // Every edge starts at its declared terminal and ends at the junction
    // (the junction is already clear of the trunk, so clearing leaves it put).
    const terminals = [t0, t1, t2]
    curves.forEach((pts, i) => {
      expect(dist3(pts[0]!, terminals[i]!)).toBeLessThan(1e-9)
      expect(dist3(pts[pts.length - 1]!, junction)).toBeLessThan(1e-9)
    })
    // Every edge clears the trunk outside its own exemption ball.
    for (const pts of curves) expect(minDistToCaps(pts, trunk, exemptPts)).toBeGreaterThanOrEqual(DELTA * 0.999)
    // The three edges of the SAME net don't cross each other's bodies away
    // from the shared junction (each is a legitimate obstacle to the others
    // once routed, and later edges must clear earlier ones of the same net).
    for (let i = 0; i < curves.length; i++) for (let j = i + 1; j < curves.length; j++) {
      const a = curves[i]!, b = curves[j]!
      for (let k = 0; k < a.length - 1; k++) {
        if (exemptPts.some((e) => dist3(a[k]!, e) < 2.5 * DELTA) || exemptPts.some((e) => dist3(a[k + 1]!, e) < 2.5 * DELTA)) continue
        for (let m = 0; m < b.length - 1; m++) {
          if (exemptPts.some((e) => dist3(b[m]!, e) < 2.5 * DELTA) || exemptPts.some((e) => dist3(b[m + 1]!, e) < 2.5 * DELTA)) continue
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
    const nets: NetIn[] = ys.map((y, i) =>
      straightNet(`wp${i}`, v3(-2, y, 0.02 * i), v3(2, y - 0.03 * i, -0.02 * i)))
    const routed = routeAll(nets, trunk, DELTA)
    const polylines = nets.map((n) => ({ id: n.id, exempt: n.anchors, pts: routed.get(n.id)![0]! }))

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
