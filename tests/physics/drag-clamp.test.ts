import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { recomputeRegions, clampDragToFeasible, settle } from '../../src/view/relax'
import { UNARY } from '../fixtures/zero-signature'

/** The worst overshoot of any content item (node disc or region circle) past the
    frame wall — >0 ⇒ something is outside the border. */

/** The worst signed overshoot of any non-root region circle past the fixed frame
    wall (>0 ⇒ a cut escapes the border). */
function worstRegionOvershoot(e: Engine): number {
  const f = e.frame
  if (f === null) return 0
  let worst = 0
  for (const [rid, g] of e.regions) {
    if (rid === e.d.root) continue
    const o = Math.max(
      g.center.x + g.radius - (f.center.x + f.half), (f.center.x - f.half) - (g.center.x - g.radius),
      g.center.y + g.radius - (f.center.y + f.half), (f.center.y - f.half) - (g.center.y - g.radius),
    )
    if (o > worst) worst = o
  }
  return worst
}

describe('clampDragToFeasible — HARD SEMANTIC CONTAINMENT (USER LAW: a drag can never pull a node into a cut it is not part of)', () => {
  it('a CUT circle stays inside the fixed border — settled AND mid-drag (USER 2026-07-06: the hard wall applies to cuts, not just discs)', () => {
    // A cut with two members; drag one member HARD at the border. The disc is
    // clamped, but the derived CUT circle (members + REGION_PAD) must ALSO stay
    // fully inside the frame — the border is a hard wall on cuts identically.
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a = h.ref(cut, 'A', UNARY)
    const b2 = h.ref(cut, 'B', UNARY)
    h.ref(h.root, 'Outer', UNARY)
    h.wire( [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: b2, port: { kind: 'arg', index: 0 } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 200) // establishes the fixed frame and a legal rest
    // settled: no cut escapes
    expect(worstRegionOvershoot(e), 'settled: no cut circle past the border').toBeLessThan(0.5)
    // mid-drag: drag member `a` far past the +x wall, frame after frame
    const ba = e.bodies.get(a)!
    const f = e.frame!
    let worst = 0
    for (let t = 1; t <= 30; t++) {
      const target = { x: f.center.x + f.half + t * 10, y: ba.pos.y }
      ba.pos = clampDragToFeasible(e, ba, target)
      recomputeRegions(e)
      worst = Math.max(worst, worstRegionOvershoot(e))
    }
    expect(worst, `mid-drag: the cut circle must not cross the border (worst overshoot ${worst.toFixed(1)} wu)`).toBeLessThan(0.5)
  })

  it('the frame-fit pull may not shove the body into a foreign cut (projections must reach a JOINT fixed point)', () => {
    // Two sibling cuts inside an outer cut. Dragging M hard past the +x wall
    // makes the outer circle spill, so the cut-wall pull drags M back toward
    // the interior — straight through the foreign cut D2's clearance. A clamp
    // that runs "circles, then wall" as one sequential pass returns that
    // penetrated point (measured 4.75 wu deep); the constraints must instead be
    // alternated until they hold together, which here means sliding M around
    // D2's clearance instead of through it.
    const h = new DiagramBuilder()
    const outer = h.cut(h.root)
    const d1 = h.cut(outer)
    const m = h.ref(d1, 'M', UNARY)
    const d2 = h.cut(outer)
    const f1 = h.ref(d2, 'F1', UNARY)
    const f2 = h.ref(d2, 'F2', UNARY)
    const e = mkEngine(h.build(), [])
    e.bodies.get(m)!.pos = { x: 50, y: 0 }
    e.bodies.get(f1)!.pos = { x: 10, y: -10 }
    e.bodies.get(f2)!.pos = { x: 10, y: 10 }
    e.frame = { center: { x: 0, y: 0 }, half: 60 }
    recomputeRegions(e)
    const bm = e.bodies.get(m)!
    const g2 = e.regions.get(d2)!
    const need = g2.radius + bm.discR * e.scale
    const basePen = need - Math.hypot(bm.pos.x - g2.center.x, bm.pos.y - g2.center.y)
    expect(basePen, 'the start position is legal').toBeLessThan(0)

    const out = clampDragToFeasible(e, bm, { x: 200, y: 0 })
    const pen = need - Math.hypot(out.x - g2.center.x, out.y - g2.center.y)
    expect(pen, `clamped position penetrates the foreign cut clearance by ${pen.toFixed(2)} wu`).toBeLessThan(0.05)
    // and the frame stayed hard for the body disc itself
    const f = e.frame!
    expect(Math.abs(out.x - f.center.x)).toBeLessThanOrEqual(f.half - bm.discR * e.scale + 1e-6)
    expect(Math.abs(out.y - f.center.y)).toBeLessThanOrEqual(f.half - bm.discR * e.scale + 1e-6)
  })
})
