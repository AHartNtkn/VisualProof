import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { recomputeRegions, clampDragToFeasible, settle } from '../../src/view/relax'

const p = (s: string) => parseTerm(s)

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
    const a = h.termNode(cut, p('a'))
    const b2 = h.termNode(cut, p('bb'))
    const outer = h.termNode(h.root, p('c')) // gives the frame some content to size against
    h.wire(cut, [{ node: a, port: { kind: 'freeVar', name: 'a' } }, { node: b2, port: { kind: 'freeVar', name: 'bb' } }])
    h.wire(h.root, [{ node: outer, port: { kind: 'freeVar', name: 'c' } }])
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


})
