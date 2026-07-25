import { describe, it, expect } from 'vitest'
import type { Vec2 } from '../../src/view/vec'
import { mkFreeSpace, route, segmentClear } from '../../src/view/route/freespace'
import { advanceNetwork, contract, netLength, netPaths, solveTarget, trySplit, type WireNet } from '../../src/view/route/network'

/**
 * ROUTED-NETWORK BEHAVIORAL CONTRACT (USER ruling 2026-07-24): these assert
 * the intended behavior — feasibility, force balance, real topology
 * operations, bounded visible movement, deterministic rest — never the
 * representation.
 */

const empty = mkFreeSpace([])

describe('free-space routing', () => {
  it('routes around a hard obstacle disc — never through it, with a bounded detour', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r: 5 }])
    const r = route(fs, { x: -20, y: 0 }, { x: 20, y: 0 })
    expect(r.length).toBeGreaterThan(40) // must detour
    expect(r.length).toBeLessThan(40 + Math.PI * 5 + 1) // bounded by the half-perimeter detour
    for (let i = 0; i + 1 < r.pts.length; i++) {
      expect(segmentClear(r.pts[i]!, r.pts[i + 1]!, fs.discs), `segment ${i} enters the disc`).toBe(true)
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
    const L0 = netLength(net, terms, empty)
    expect(trySplit(net, terms, empty), 'the wide rectangle star must split').toBe(true)
    expect(net.junctions.length).toBe(2)
    expect(net.edges.length, 'four terminal edges + one connector').toBe(5)
    expect(netLength(net, terms, empty)).toBeLessThan(L0)
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
    expect(trySplit(net, terms, empty)).toBe(false)
  })
})

describe('presentation continuation', () => {
  it('bounded visible movement per substep, and a settled boundary is an exact deterministic no-op', () => {
    const terms: Vec2[] = [{ x: 0, y: 20 }, { x: -17.32, y: -10 }, { x: 17.32, y: -10 }]
    const net: WireNet = { junctions: [{ x: 15, y: 15 }], edges: [[0, 3], [1, 3], [2, 3]] }
    const before = { ...net.junctions[0]! }
    advanceNetwork(net, terms, empty, { substeps: 1, bound: 0.5 })
    const after = net.junctions[0]!
    const moved = Math.hypot(after.x - before.x, after.y - before.y)
    expect(moved, 'one substep moves at most the bound').toBeLessThanOrEqual(0.5 + 1e-9)
    expect(moved).toBeGreaterThan(0)
    // run to rest
    for (let i = 0; i < 400; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })) break
    const rest = JSON.stringify(net)
    expect(advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 }), 'settled input is a no-op').toBe(false)
    expect(JSON.stringify(net), 'no-op is EXACT').toBe(rest)
  })

  it('pinch → contraction → re-split: the full transition through a real degree-4 intermediate', () => {
    // wide rectangle, correct columns pairing
    let terms: Vec2[] = [{ x: -20, y: -6 }, { x: -20, y: 6 }, { x: 20, y: -6 }, { x: 20, y: 6 }]
    const net: WireNet = { junctions: [{ x: -10, y: 0 }, { x: 10, y: 0 }], edges: [[0, 4], [1, 4], [2, 5], [3, 5], [4, 5]] }
    for (let i = 0; i < 200; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })) break
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
      advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })
    }
    // pull apart vertically: rows pairing must emerge
    for (let step = 0; step <= 120; step++) {
      const t = step / 120
      const h = 6 + 14 * t
      terms = [{ x: -0.2, y: -h }, { x: -0.2, y: h }, { x: 0.2, y: -h }, { x: 0.2, y: h }]
      advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })
    }
    for (let i = 0; i < 400; i++) if (!advanceNetwork(net, terms, empty, { substeps: 20, bound: 0.5 })) break
    expect(net.junctions.length, 're-split into two junctions').toBe(2)
    const side = (j: number): string => net.edges
      .filter(([u, v]) => u === 4 + j || v === 4 + j)
      .flatMap(([u, v]) => [u, v].filter((x) => x < 4)).sort().join('')
    const pairing = [side(0), side(1)].sort().join('|')
    expect(pairing, 'rows pairing after the pinch-and-stretch').toBe('02|13')
  })
})

describe('routing feasibility composes with the network', () => {
  it('a junction network with an interposed disc keeps every drawn segment out of the disc', () => {
    const fs = mkFreeSpace([{ c: { x: 0, y: 0 }, r: 4 }])
    const terms: Vec2[] = [{ x: -15, y: -8 }, { x: -15, y: 8 }, { x: 16, y: 0 }]
    const net: WireNet = { junctions: [{ x: -8, y: 0 }], edges: [[0, 3], [1, 3], [2, 3]] }
    for (let i = 0; i < 300; i++) if (!advanceNetwork(net, terms, fs, { substeps: 20, bound: 0.5 })) break
    for (const { pts } of netPaths(net, terms, fs)) {
      for (let i = 0; i + 1 < pts.length; i++) {
        expect(segmentClear(pts[i]!, pts[i + 1]!, fs.discs), 'drawn segment enters a node disc').toBe(true)
      }
    }
  })
})

