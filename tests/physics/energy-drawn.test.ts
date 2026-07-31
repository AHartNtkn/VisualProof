import { describe, it, expect } from 'vitest'
import { mkFreeSpace } from '../../src/view/route/freespace'
import type { Vec2 } from '../../src/view/vec'
import { netEval } from '../../src/view/route/network'
import type { WireNet } from '../../src/view/route/network'

/**
 * ENERGY-DRAWN WIRES (spec 2026-07-31, USER-confirmed design statement): a
 * wire's visible curve is the minimizer of the one energy — length, bending,
 * and NEARNESS to things — so a resting wire passes obstacles at a
 * comfortable standoff in a gentle sweep. It never tracks a boundary (the
 * taut-band look, rejected 2026-07-05 and 2026-07-31), and it bends away
 * from things it merely passes near, without any detour.
 *
 * The standoff is emergent: nearness is charged by the SAME falloff wires
 * already pay against each other (radius R = sepR·scale), so the resting gap
 * is where shortening stops paying for the nearness it buys — no constant
 * anywhere sets it.
 */

const beta = 5.5 * 5.5 // r*² at scale 1 (the ruled bending stiffness)
const nsFor = (discs: { c: Vec2; r: number }[]) => ({ discs, bounds: null, R: 5, slope: 1.4 })

/** Min gap between drawn segments and a disc's boundary (negative = inside);
    measured segment-to-center, so the closest approach between samples counts. */
function minGap(segs: readonly { a: Vec2; b: Vec2 }[], c: Vec2, r: number): number {
  let g = Infinity
  for (const s of segs) {
    const vx = s.b.x - s.a.x, vy = s.b.y - s.a.y
    const vv = vx * vx + vy * vy
    const t = vv < 1e-18 ? 0 : Math.max(0, Math.min(1, ((c.x - s.a.x) * vx + (c.y - s.a.y) * vy) / vv))
    g = Math.min(g, Math.hypot(s.a.x + vx * t - c.x, s.a.y + vy * t - c.y) - r)
  }
  return g
}

describe('energy-drawn wires: nearness is charged, standoff is emergent', () => {
  it('a resting detour stands off from the disc it rounds — it never rides the boundary', () => {
    // Two terminals on a line through a disc: the wire must go around. Under
    // the boundary-pressed construction the drawn curve rides the clearance
    // circle (gap ≈ the 1.5 routing clearance); under the energy the resting
    // gap balances tension against the nearness falloff (R = 5) and rests
    // well clear of it.
    const disc = { c: { x: 0, y: 0 }, r: 20 }
    const fs = mkFreeSpace([{ c: disc.c, r: disc.r + 1.5 }], null)
    const terms: Vec2[] = [{ x: -60, y: 0 }, { x: 60, y: 0 }]
    const net: WireNet = { junctions: [], edges: [[0, 1]] }
    const { segs } = netEval(net, terms, fs, nsFor([disc]), [], beta)
    const g = minGap(segs, disc.c, disc.r)
    expect(g, `resting gap ${g.toFixed(2)} — the curve is pressed against the boundary`).toBeGreaterThanOrEqual(2.5)
  })

  it('a wire bends away from a disc it merely passes near — no detour required', () => {
    // The straight segment clears the routing obstacle, so the old pipeline
    // draws it dead straight at gap 2. Nearness costs, so the minimizer bows
    // away and widens the gap.
    const disc = { c: { x: 0, y: -22 }, r: 20 } // straight line passes at gap 2
    const fs = mkFreeSpace([{ c: disc.c, r: disc.r + 1.5 }], null)
    const terms: Vec2[] = [{ x: -60, y: 0 }, { x: 60, y: 0 }]
    const net: WireNet = { junctions: [], edges: [[0, 1]] }
    const { segs } = netEval(net, terms, fs, nsFor([disc]), [], beta)
    const g = minGap(segs, disc.c, disc.r)
    expect(g, `gap ${g.toFixed(2)} — the wire did not yield to the nearby disc`).toBeGreaterThan(2.6)
  })
})
