import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { carryOver } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, clampDragToFeasible, settle, establishProofFrame, establishFrame } from '../../src/view/relax'

const p = (s: string) => parseTerm(s)

/** The worst overshoot of any content item (node disc or region circle) past the
    frame wall — >0 ⇒ something is outside the border. */
function worstContentOvershoot(e: Engine): number {
  const f = e.frame!
  let worst = 0
  const check = (cx: number, cy: number, r: number): void => {
    const o = Math.max(cx + r - (f.center.x + f.half), (f.center.x - f.half) - (cx - r),
      cy + r - (f.center.y + f.half), (f.center.y - f.half) - (cy - r))
    if (o > worst) worst = o
  }
  for (const b of e.bodies.values()) if (!b.id.startsWith('e:')) check(b.pos.x, b.pos.y, b.discR * e.scale)
  for (const [rid, g] of e.regions) if (rid !== e.d.root) check(g.center.x, g.center.y, g.radius)
  return worst
}

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

  it('the border is sized ONCE from the proof-wide max extent: byte-identical across ALL steps, every step fits (USER RULING 2026-07-06 option a)', () => {
    // A synthetic "replay": three diagrams of increasing size (the largest is the
    // binding step). The border is sized ONCE from the proof-wide max content extent,
    // is byte-identical no matter which step is displayed, and EVERY step's content
    // fits inside it.
    const mk = (n: number): { d: ReturnType<DiagramBuilder['build']>; b: string[] } => {
      const h = new DiagramBuilder()
      for (let i = 0; i < n; i++) { const t = h.termNode(h.root, p(`x${i}`)); h.wire(h.root, [{ node: t, port: { kind: 'freeVar', name: `x${i}` } }]) }
      return { d: h.build(), b: [] }
    }
    const steps = [mk(1), mk(4), mk(9)].map((s) => ({ diagram: s.d, boundary: s.b }))
    const e0 = mkEngine(steps[0]!.diagram, steps[0]!.boundary)
    establishProofFrame(e0, steps)
    const f = e0.frame!
    expect(f.half).toBeGreaterThan(0)
    // every step: build, project, and confirm all content is inside the fixed border
    for (const s of steps) {
      const se = mkEngine(s.diagram, s.boundary)
      recomputeRegions(se); resolveOverlaps(se); recomputeRegions(se)
      se.frame = f // the fixed border (as carryOver would supply)
      expect(worstContentOvershoot(se), 'every step fits the fixed border (projected)').toBeLessThan(0.5)
    }
    // the binding (largest) step also fits when fully SETTLED (settling compacts, so
    // the projected-extent border is a safe over-bound)
    const eL = mkEngine(steps[2]!.diagram, steps[2]!.boundary)
    eL.frame = f
    settle(eL, 200)
    expect(worstContentOvershoot(eL), 'the largest step fits the border when settled').toBeLessThan(0.5)
    // byte-identical border across a rewrite: a rebuilt engine that carries the frame
    // keeps it exactly, and establishFrame does NOT recompute it
    const e1 = mkEngine(steps[1]!.diagram, steps[1]!.boundary)
    carryOver(e0, e1)
    recomputeRegions(e1); resolveOverlaps(e1); establishFrame(e1)
    expect(e1.frame).toEqual(f)
  })

})
