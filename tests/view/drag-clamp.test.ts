import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, clampDragToFeasible } from '../../src/view/relax'

const p = (s: string) => parseTerm(s)

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
