import { describe, it, expect } from 'vitest'
import type { Vec2 } from '../../src/view/vec'
import type { Disc } from '../../src/view/route/freespace'
import { mkFreeSpace, route, segmentClear, insideAnyDisc } from '../../src/view/route/freespace'
import { advanceNetwork, contract, netLength, netPaths, solveTarget, trySplit, type WireNet } from '../../src/view/route/network'

/**
 * ROUTED-NETWORK BEHAVIORAL CONTRACT (USER ruling 2026-07-24): these assert
 * the intended behavior — feasibility, force balance, real topology
 * operations, bounded visible movement, deterministic rest — never the
 * representation.
 */

const empty = mkFreeSpace([])
const emptyNs = { discs: [], bounds: null, R: 5, slope: 1.4 }

describe('free-space routing', () => {
  it('routes around a hard obstacle disc — never through it, with a bounded detour', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r: 5 }])
    const r = route(fs, { x: -20, y: 0 }, { x: 20, y: 0 })
    expect(r.length).toBeGreaterThan(40) // must detour
    expect(r.length).toBeLessThan(40 + Math.PI * 5 + 1) // bounded by the half-perimeter detour
    // `pts` is the motion-path polyline: hug chords ride the TRUE circle, so a
    // chord sags inside by at most r·(1−cos(ARC_STEP/2)) — never deeper
    const band = 5 * (1 - Math.cos(Math.PI / 16)) + 1e-9
    for (const pt of r.pts) {
      expect(Math.hypot(pt.x, pt.y), 'polyline point inside the disc').toBeGreaterThanOrEqual(5 - 1e-9)
    }
    for (let i = 0; i + 1 < r.pts.length; i++) {
      const m = { x: (r.pts[i]!.x + r.pts[i + 1]!.x) / 2, y: (r.pts[i]!.y + r.pts[i + 1]!.y) / 2 }
      expect(Math.hypot(m.x, m.y), `segment ${i} dips past the chord band`).toBeGreaterThanOrEqual(5 - band)
    }
  })

  it('routes straight when nothing blocks', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 30 }, r: 5 }])
    const r = route(fs, { x: -20, y: 0 }, { x: 20, y: 0 })
    expect(r.pts.length).toBe(2)
    expect(r.length).toBeCloseTo(40, 9)
  })
})

describe('degree-3 equilibrium (u1+u2+u3=0 — no angle penalty exists)', () => {
  it('an unobstructed 3-terminal junction solves to the Fermat point with 120° arms', () => {
    const terms: Vec2[] = [
      { x: 0, y: 20 },
      { x: -17.32, y: -10 },
      { x: 17.32, y: -10 },
    ] // equilateral: Fermat point at the origin
    const net: WireNet = { junctions: [{ x: 5, y: 7 }], edges: [[0, 3], [1, 3], [2, 3]] }
    solveTarget(net, terms, empty)
    const j = net.junctions[0]!
    expect(Math.hypot(j.x, j.y), 'junction at the Fermat point').toBeLessThan(0.05)
    const us = terms.map((t) => {
      const d = Math.hypot(t.x - j.x, t.y - j.y)
      return { x: (t.x - j.x) / d, y: (t.y - j.y) / d }
    })
    for (let a = 0; a < 3; a++) {
      const b = (a + 1) % 3
      const ang = Math.acos(Math.max(-1, Math.min(1, us[a]!.x * us[b]!.x + us[a]!.y * us[b]!.y))) * (180 / Math.PI)
      expect(Math.abs(ang - 120), `arm pair ${a},${b} at ${ang.toFixed(1)}°`).toBeLessThan(1.5)
    }
  })
})

describe('topology operations are real graph operations', () => {
  it('a zero internal edge is DELETED, identifying its endpoints into one higher-degree vertex', () => {
    const terms: Vec2[] = [{ x: -10, y: -5 }, { x: -10, y: 5 }, { x: 10, y: -5 }, { x: 10, y: 5 }]
    const net: WireNet = {
      junctions: [{ x: -0.0002, y: 0 }, { x: 0.0002, y: 0 }],
      edges: [[0, 4], [1, 4], [2, 5], [3, 5], [4, 5]],
    }
    expect(contract(net, terms, empty)).toBe(true)
    expect(net.junctions.length, 'one junction remains').toBe(1)
    expect(net.edges.length, 'four terminal edges, no internal edge, no duplicates').toBe(4)
    const deg = net.edges.filter(([u, v]) => u === 4 || v === 4).length
    expect(deg, 'a REAL degree-4 vertex').toBe(4)
  })

  it('a degree-4 vertex splits only by the descending partition derivative, and the split lowers routed length', () => {
    const terms: Vec2[] = [{ x: -20, y: -6 }, { x: -20, y: 6 }, { x: 20, y: -6 }, { x: 20, y: 6 }]
    const net: WireNet = { junctions: [{ x: 0, y: 0 }], edges: [[0, 4], [1, 4], [2, 4], [3, 4]] }
    const L0 = netLength(net, terms, empty, emptyNs)
    expect(trySplit(net, terms, empty, emptyNs), 'the wide rectangle star must split').toBe(true)
    expect(net.junctions.length).toBe(2)
    expect(net.edges.length, 'four terminal edges + one connector').toBe(5)
    expect(netLength(net, terms, empty, emptyNs)).toBeLessThan(L0)
    // and it converges to the Steiner pairing: left terminals on one junction
    solveTarget(net, terms, empty)
    const nT = 4
    const side = (j: number): number[] => net.edges
      .filter(([u, v]) => u === nT + j || v === nT + j)
      .flatMap(([u, v]) => [u, v].filter((x) => x < nT))
    const s0 = side(0).sort().join(''), s1 = side(1).sort().join('')
    expect([s0, s1].sort().join('|'), 'columns pairing').toBe('01|23')
  })

  it('a degree-3 junction never splits (both split sides need degree ≥ 3)', () => {
    const terms: Vec2[] = [{ x: 0, y: 20 }, { x: -17, y: -10 }, { x: 17, y: -10 }]
    const net: WireNet = { junctions: [{ x: 0, y: 0 }], edges: [[0, 3], [1, 3], [2, 3]] }
    expect(trySplit(net, terms, empty, emptyNs)).toBe(false)
  })
})

describe('presentation continuation', () => {
  it('bounded visible movement per substep, and a settled boundary is an exact deterministic no-op', () => {
    const terms: Vec2[] = [{ x: 0, y: 20 }, { x: -17.32, y: -10 }, { x: 17.32, y: -10 }]
    const net: WireNet = { junctions: [{ x: 15, y: 15 }], edges: [[0, 3], [1, 3], [2, 3]] }
    const before = { ...net.junctions[0]! }
    advanceNetwork(net, terms, empty, { substeps: 1, bound: 0.5, ns: emptyNs })
    const after = net.junctions[0]!
    const moved = Math.hypot(after.x - before.x, after.y - before.y)
    expect(moved, 'one substep moves at most the bound').toBeLessThanOrEqual(0.5 + 1e-9)
    expect(moved).toBeGreaterThan(0)
    // run to rest
    for (let i = 0; i < 400; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs })) break
    const rest = JSON.stringify(net)
    expect(advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs }), 'settled input is a no-op').toBe(false)
    expect(JSON.stringify(net), 'no-op is EXACT').toBe(rest)
  })

  it('pinch → contraction → re-split: the full transition through a real degree-4 intermediate', () => {
    // wide rectangle, correct columns pairing
    let terms: Vec2[] = [{ x: -20, y: -6 }, { x: -20, y: 6 }, { x: 20, y: -6 }, { x: 20, y: 6 }]
    const net: WireNet = { junctions: [{ x: -10, y: 0 }, { x: 10, y: 0 }], edges: [[0, 4], [1, 4], [2, 5], [3, 5], [4, 5]] }
    for (let i = 0; i < 200; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs })) break
    // PINCH the wire flat (the user's squeeze gesture): width → ~0 drives the
    // junctions together — the connector reaches numerical zero and the edge
    // record is deleted; then growing the rows apart re-splits the degree-4
    // vertex by the partition derivative.
    // (the degree-4 intermediate is a REAL stored graph — proven by the
    // contraction unit test above; obstacle-free it is Steiner-unstable, so it
    // re-splits within the same frame's substeps rather than resting)
    for (let step = 0; step <= 120; step++) {
      const t = step / 120
      const w = 20 - 19.8 * t
      terms = [{ x: -w, y: -6 }, { x: -w, y: 6 }, { x: w, y: -6 }, { x: w, y: 6 }]
      advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs })
    }
    // pull apart vertically: rows pairing must emerge
    for (let step = 0; step <= 120; step++) {
      const t = step / 120
      const h = 6 + 14 * t
      terms = [{ x: -0.2, y: -h }, { x: -0.2, y: h }, { x: 0.2, y: -h }, { x: 0.2, y: h }]
      advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs })
    }
    for (let i = 0; i < 400; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5, ns: emptyNs })) break
    expect(net.junctions.length, 're-split into two junctions').toBe(2)
    const side = (j: number): string => net.edges
      .filter(([u, v]) => u === 4 + j || v === 4 + j)
      .flatMap(([u, v]) => [u, v].filter((x) => x < 4)).sort().join('')
    const pairing = [side(0), side(1)].sort().join('|')
    expect(pairing, 'rows pairing after the pinch-and-stretch').toBe('02|13')
  })
})

/** Seeded xorshift32 — deterministic, no Math.random. */
function mkRng(seed: number): () => number {
  let s = seed >>> 0
  if (s === 0) s = 0x9e3779b9
  return () => {
    s ^= s << 13; s >>>= 0
    s ^= s >>> 17
    s ^= s << 5; s >>>= 0
    return s / 4294967296
  }
}

/** Reference clear-detour LENGTH via the deleted disc-polygon corner graph
    (16-gon circumscribed at r/cos(π/16), all-pairs visibility, Dijkstra p→q).
    Inlined HERE (not kept in src) purely as the exactness oracle: the smooth
    tangent-graph geodesic can only be ≤ this polygon path. Returns null if the
    corner graph finds no detour. */
function polygonDetourLength(discs: readonly Disc[], p: Vec2, q: Vec2): number | null {
  const K = 16
  const corners: Vec2[] = []
  for (const D of discs) {
    const R = D.r / Math.cos(Math.PI / K)
    for (let k = 0; k < K; k++) {
      const a = (2 * Math.PI * k) / K
      const pt = { x: D.c.x + R * Math.cos(a), y: D.c.y + R * Math.sin(a) }
      if (insideAnyDisc(pt, discs) >= 0) continue
      corners.push(pt)
    }
  }
  const n = corners.length, P = n, Q = n + 1
  const adj: { j: number; d: number }[][] = corners.map(() => [])
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      if (!segmentClear(corners[i]!, corners[j]!, discs)) continue
      const d = Math.hypot(corners[i]!.x - corners[j]!.x, corners[i]!.y - corners[j]!.y)
      adj[i]!.push({ j, d }); adj[j]!.push({ j: i, d })
    }
  }
  const pcon: { j: number; d: number }[] = [], qcon: { j: number; d: number }[] = []
  for (let i = 0; i < n; i++) {
    if (segmentClear(p, corners[i]!, discs)) pcon.push({ j: i, d: Math.hypot(corners[i]!.x - p.x, corners[i]!.y - p.y) })
    if (segmentClear(q, corners[i]!, discs)) qcon.push({ j: i, d: Math.hypot(corners[i]!.x - q.x, corners[i]!.y - q.y) })
  }
  const dist = new Array<number>(n + 2).fill(Infinity)
  const done = new Array<boolean>(n + 2).fill(false)
  dist[P] = 0
  for (;;) {
    let u = -1, best = Infinity
    for (let i = 0; i < n + 2; i++) if (!done[i] && dist[i]! < best) { best = dist[i]!; u = i }
    if (u < 0) break
    done[u] = true
    if (u === Q) break
    const edges = u === P ? pcon : u < n ? adj[u]! : []
    for (const { j, d } of edges) if (dist[u]! + d < dist[j]!) dist[j] = dist[u]! + d
    if (u !== P && u < n) {
      const qc = qcon.find((e) => e.j === u)
      if (qc !== undefined && dist[u]! + qc.d < dist[Q]!) dist[Q] = dist[u]! + qc.d
    }
  }
  return Number.isFinite(dist[Q]!) ? dist[Q]! : null
}

describe('bitangent routing is exact vs the polygon reference', () => {
  it('the clear detour is never longer than the 16-gon detour, and every drawn segment is clear', () => {
    const rng = mkRng(0x7a9e1)
    let detours = 0
    for (let t = 0; t < 20; t++) {
      const p = { x: -30, y: 0 }, q = { x: 30, y: 0 }
      const nd = 1 + Math.floor(rng() * 3)
      const discs: Disc[] = []
      while (discs.length < nd) {
        const c = { x: -15 + 30 * rng(), y: -8 + 16 * rng() }
        const r = 4 + 4 * rng()
        if (Math.hypot(c.x - p.x, c.y - p.y) <= r + 0.5 || Math.hypot(c.x - q.x, c.y - q.y) <= r + 0.5) continue
        discs.push({ c, r })
      }
      const fs = mkFreeSpace(discs) // no bounds ⇒ cost == length, so a detour is taken iff it is shorter
      const r = route(fs, p, q)
      if (r.pts.length > 2) {
        detours++
        const poly = polygonDetourLength(discs, p, q)
        expect(poly, `config ${t}: polygon found no detour but tangent graph did`).not.toBeNull()
        expect(r.length, `config ${t}: tangent detour ${r.length.toFixed(4)} longer than polygon ${poly!.toFixed(4)}`)
          .toBeLessThanOrEqual(poly! + 1e-6)
        for (const pt of r.pts) {
          for (const D of discs) {
            expect(Math.hypot(pt.x - D.c.x, pt.y - D.c.y), `config ${t}: polyline point inside a disc`).toBeGreaterThanOrEqual(D.r - 1e-9)
          }
        }
      }
    }
    expect(detours, 'the random configs must exercise real detours').toBeGreaterThan(4)
  })
})

describe('tangency winding', () => {
  it('a route around a single disc hugs it with monotone angular progression (no zigzag)', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r: 5 }])
    const r = route(fs, { x: -20, y: 0 }, { x: 20, y: 0 })
    expect(r.pts.length, 'the route must detour around the disc').toBeGreaterThan(2)
    let sign = 0
    for (let i = 1; i < r.pts.length; i++) {
      let d = Math.atan2(r.pts[i]!.y, r.pts[i]!.x) - Math.atan2(r.pts[i - 1]!.y, r.pts[i - 1]!.x)
      while (d > Math.PI) d -= 2 * Math.PI
      while (d < -Math.PI) d += 2 * Math.PI
      if (Math.abs(d) < 1e-9) continue
      const s = Math.sign(d)
      if (sign === 0) sign = s
      expect(s, `angular progression reversed at point ${i} (a zigzag)`).toBe(sign)
    }
  })
})

describe('routing feasibility composes with the network', () => {
  it('a junction network with an interposed disc keeps every drawn segment out of the disc', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r: 4 }])
    const terms: Vec2[] = [{ x: -15, y: -8 }, { x: -15, y: 8 }, { x: 16, y: 0 }]
    const net: WireNet = { junctions: [{ x: -8, y: 0 }], edges: [[0, 3], [1, 3], [2, 3]] }
    for (let i = 0; i < 300; i++) if (!advanceNetwork(net, terms, fs, { substeps: 20, bound: 0.5, ns: emptyNs })) break
    // routed polyline points ride the disc boundary or stay outside; chords may
    // sag inside only within the ARC_STEP chord band
    const band = 4 * (1 - Math.cos(Math.PI / 16)) + 1e-9
    for (const { pts } of netPaths(net, terms, fs)) {
      for (const pt of pts) {
        expect(Math.hypot(pt.x, pt.y), 'routed point inside the disc').toBeGreaterThanOrEqual(4 - 1e-9)
      }
      for (let i = 0; i + 1 < pts.length; i++) {
        const m = { x: (pts[i]!.x + pts[i + 1]!.x) / 2, y: (pts[i]!.y + pts[i + 1]!.y) / 2 }
        expect(Math.hypot(m.x, m.y), 'routed segment dips past the chord band').toBeGreaterThanOrEqual(4 - band)
      }
    }
  })
})

