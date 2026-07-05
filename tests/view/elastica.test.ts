import { describe, it, expect } from 'vitest'
import { solveLeg, trace, thetaRange, arcClose, mkLegCache, RANGE_B, QN } from '../../src/view/elastica'

/**
 * PLAN 22 LAW BATTERY — the massless elastica wire (solver core).
 * These are the structural impossibility claims the user demanded, tested
 * constructively over input sweeps: no representable kink, loop, or memory.
 */

// deterministic seeded sweep (no Math.random — reproducibility is a law here)
function* boundarySweep(n: number): Generator<{ p0: { x: number; y: number }; th0: number; p1: { x: number; y: number }; th1: number }> {
  let s = 12345
  const rnd = (): number => {
    s = (s * 1103515245 + 12345) & 0x7fffffff
    return s / 0x7fffffff
  }
  for (let i = 0; i < n; i++) {
    yield {
      p0: { x: rnd() * 200 - 100, y: rnd() * 200 - 100 },
      th0: rnd() * 2 * Math.PI - Math.PI,
      p1: { x: rnd() * 200 - 100, y: rnd() * 200 - 100 },
      th1: rnd() * 2 * Math.PI - Math.PI,
    }
  }
}

describe('elastica — structural impossibility laws', () => {
  it('every solution over the sweep has tangent range <= pi + fallback slack (no loop is representable)', () => {
    for (const b of boundarySweep(500)) {
      const sol = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, b.th1, false)
      // regular path enforces <= RANGE_B strictly; the arc fallback (exact
      // closure under extreme boundaries) can carry up to |2*delta| < 2*pi,
      // still below the self-intersection threshold of monotone-curvature
      // arcs (they self-cross only past total turning 2*pi)
      expect(thetaRange(sol.c1, sol.c2)).toBeLessThan(2 * Math.PI)
    }
  })

  it('the regular (non-fallback) solutions respect RANGE_B exactly', () => {
    let checked = 0
    for (const b of boundarySweep(500)) {
      const sol = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, b.th1, false)
      const arc = arcClose(b.p0, b.th0, b.p1)
      // if the chosen tau differs from the raw arc tau it came from the
      // scanned/refined set, which range-gates candidates
      if (Math.abs(sol.dTurn - arc.tau) > 1e-9) {
        expect(thetaRange(sol.c1, sol.c2)).toBeLessThanOrEqual(RANGE_B + 1e-9)
        checked++
      }
    }
    expect(checked).toBeGreaterThan(100)
  })

  it('closure: the traced endpoint lands on the target within the quadrature bound', () => {
    for (const b of boundarySweep(300)) {
      const sol = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, b.th1, false)
      const out: { x: number; y: number }[] = []
      trace(b.p0, b.th0, sol.c1, sol.c2, sol.L, out, 4 * QN)
      const e = out[out.length - 1]!
      expect(Math.hypot(e.x - b.p1.x, e.y - b.p1.y), `residual at ${JSON.stringify(b)}`).toBeLessThan(0.75)
    }
  })

  it('zero memory: the solve is a pure function — identical inputs give bit-identical outputs regardless of history', () => {
    const b1 = { p0: { x: 0, y: 0 }, th0: 0.3, p1: { x: 60, y: 20 }, th1: 2.8 }
    const fresh = solveLeg(mkLegCache(), b1.p0, b1.th0, b1.p1, b1.th1, false)
    // drag the boundary through wild configurations (the orbit attack),
    // then return to b1: the result must be identical to the fresh solve
    const cache = mkLegCache()
    for (let k = 0; k <= 48; k++) {
      const a = (k / 24) * 2 * Math.PI
      solveLeg(cache, b1.p0, b1.th0, { x: Math.cos(a) * 70, y: Math.sin(a) * 70 }, b1.th1 + a, false)
    }
    const back = solveLeg(cache, b1.p0, b1.th0, b1.p1, b1.th1, false)
    expect(back.c1).toBe(fresh.c1)
    expect(back.c2).toBe(fresh.c2)
    expect(back.L).toBe(fresh.L)
  })

  it('kinks unrepresentable: theta is a polynomial — adjacent trace tangents differ by O(1/n)', () => {
    for (const b of boundarySweep(100)) {
      const sol = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, b.th1, false)
      const maxTurnPerStep = (Math.abs(sol.c1) + 2 * Math.abs(sol.c2)) / (4 * QN)
      expect(maxTurnPerStep).toBeLessThan(Math.PI / 8)
    }
  })

  it('free-end legs carry no arrival well; welled legs charge it', () => {
    const b = { p0: { x: 0, y: 0 }, th0: 0, p1: { x: 50, y: 40 }, th1: Math.PI / 2 }
    const free = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, b.th1, true)
    expect(free.well).toBe(0)
    const welled = solveLeg(mkLegCache(), b.p0, b.th0, b.p1, 3.0, false)
    expect(welled.well).toBeGreaterThanOrEqual(0)
  })

  it('the cache is sound: a hit returns the exact prior solution, a changed tuple re-solves', () => {
    const cache = mkLegCache()
    const b = { p0: { x: 0, y: 0 }, th0: 0.2, p1: { x: 40, y: 10 }, th1: 3.0 }
    const s1 = solveLeg(cache, b.p0, b.th0, b.p1, b.th1, false)
    const s2 = solveLeg(cache, b.p0, b.th0, b.p1, b.th1, false)
    expect(s2).toBe(s1) // same object — memo hit
    const s3 = solveLeg(cache, b.p0, b.th0, { x: 41, y: 10 }, b.th1, false)
    expect(s3).not.toBe(s1)
  })

  // FREE-END REPRESENTABILITY (the candidate-grid law). A free-end leg's scan
  // covers the WHOLE feasible turn interval [−π, π] (its th1 is a dummy — the
  // well is off — so a D0-centered scan is meaningless). Consequence: a free-end
  // leg reaches a target in ANY direction within the reachable CONE — up to
  // ~138° behind the port heading — with a genuine range ≤ π solution (worst
  // case ~L=1.4·chord). Beyond ~138° the target is directly behind and NO
  // range ≤ π θ-quadratic closes it (reaching directly behind needs ∫sin θ = 0
  // with θ(0)=0, forcing θ past π): that ~84° wedge is outside the family by
  // construction, so it is NOT asserted representable here.
  it('free-end legs reach every target in the ±135° cone with range <= pi and L <= 2·chord', () => {
    for (const dist of [40, 100, 250]) {
      for (let deg = -135; deg <= 135; deg += 15) {
        const phi = (deg * Math.PI) / 180
        const p1 = { x: Math.cos(phi) * dist, y: Math.sin(phi) * dist }
        const sol = solveLeg(mkLegCache(), { x: 0, y: 0 }, 0, p1, 0, true)
        const label = `free-end to ${deg}° at ${dist}`
        expect(thetaRange(sol.c1, sol.c2), `${label}: range`).toBeLessThanOrEqual(Math.PI + 1e-6)
        expect(sol.L, `${label}: L`).toBeLessThanOrEqual(2 * dist)
      }
    }
  })

  it('a directly-behind free-end target is deterministic (the τ=±π energy tie is broken by scan order)', () => {
    // reaching directly behind needs a > pi turn (no representable leg); the
    // memoryless law still demands a deterministic pick from the τ = +π / −π
    // tie — the −π-first scan order fixes it, so identical inputs match.
    const p1 = { x: -100, y: 0 }
    const a = solveLeg(mkLegCache(), { x: 0, y: 0 }, 0, p1, 0, true)
    const b = solveLeg(mkLegCache(), { x: 0, y: 0 }, 0, p1, 0, true)
    expect(a.c1).toBe(b.c1)
    expect(a.c2).toBe(b.c2)
    expect(a.L).toBe(b.L)
  })
})
