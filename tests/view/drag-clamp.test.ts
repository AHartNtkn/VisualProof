import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, clampDragToFeasible, settle } from '../../src/view/relax'

const p = (s: string) => parseTerm(s)

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
  // A root node dragged straight at a sibling cut's centre must stay clamped
  // OUTSIDE that cut circle at every frame — crossing the boundary would change
  // what the diagram means, and that must not happen even transiently.
  it('a root node dragged into a sibling cut circle is clamped outside at every frame', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('a')) // on the sheet
    const cut = h.cut(h.root)
    const b = h.termNode(cut, p('b')) // inside the cut
    h.wire(h.root, [{ node: a, port: { kind: 'freeVar', name: 'a' } }])
    h.wire(cut, [{ node: b, port: { kind: 'freeVar', name: 'b' } }])
    const e = mkEngine(h.build(), [])
    recomputeRegions(e)
    resolveOverlaps(e) // a legal, separated start (the construction projection)
    recomputeRegions(e)

    const ba = e.bodies.get(a)!
    // the cut's derived circle (a is NOT a member of it)
    const cutG = e.regions.get(cut)!
    const start = { x: ba.pos.x, y: ba.pos.y }
    // sweep the cursor from a's rest position straight through the cut centre and
    // out the far side — the hard case (the user "dragging hard at a cut boundary")
    const far = { x: cutG.center.x + (cutG.center.x - start.x), y: cutG.center.y + (cutG.center.y - start.y) }
    let observed = 0
    let maxPush = 0
    for (let t = 0; t <= 40; t++) {
      const f = t / 40
      const target = { x: start.x + (far.x - start.x) * f, y: start.y + (far.y - start.y) * f }
      const clamped = clampDragToFeasible(e, ba, target)
      const d = Math.hypot(clamped.x - cutG.center.x, clamped.y - cutG.center.y)
      // the node's disc must not enter the cut circle: centre distance >= cut radius
      // (a node whose centre is inside the cut circle reads as being IN the cut)
      expect(d, `frame ${t}: node centre must stay outside the cut circle`).toBeGreaterThanOrEqual(cutG.radius - 1e-6)
      maxPush = Math.max(maxPush, Math.hypot(clamped.x - target.x, clamped.y - target.y))
      observed++
    }
    expect(observed).toBe(41)
    // the clamp actually engaged: the raw path aimed straight through the cut centre,
    // so a no-op clamp would leave the target untouched — the clamp must have pushed
    // it out by at least the cut radius somewhere along the sweep
    expect(maxPush, 'the clamp engaged (the raw path aimed through the cut centre)').toBeGreaterThan(cutG.radius)
  })

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

  it('a node dragged within its OWN region is never clamped (its region follows it)', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const a = h.termNode(cut, p('a')) // member of the cut
    h.wire(cut, [{ node: a, port: { kind: 'freeVar', name: 'a' } }])
    const e = mkEngine(h.build(), [])
    recomputeRegions(e)
    const ba = e.bodies.get(a)!
    // dragging a far in any direction: a is inside its own region (the cut) and the
    // cut is derived around it, so the clamp (which exempts ancestors) is a no-op
    for (const target of [{ x: 200, y: 0 }, { x: -150, y: 90 }, { x: 0, y: -300 }]) {
      const clamped = clampDragToFeasible(e, ba, target)
      expect(Math.hypot(clamped.x - target.x, clamped.y - target.y), 'own-region drag is unclamped').toBeLessThan(1e-6)
    }
  })
})
