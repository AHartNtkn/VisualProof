import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, clampDragToFeasible } from '../../src/view/relax'

describe('clampDragToFeasible semantic containment', () => {
  it('keeps a root node outside a sibling cut at every drag frame', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, parseTerm('a'))
    const cut = h.cut(h.root)
    const b = h.termNode(cut, parseTerm('b'))
    h.wire(h.root, [{ node: a, port: { kind: 'freeVar', name: 'a' } }])
    h.wire(cut, [{ node: b, port: { kind: 'freeVar', name: 'b' } }])
    const engine = mkEngine(h.build(), [])
    recomputeRegions(engine)
    resolveOverlaps(engine)
    recomputeRegions(engine)

    const body = engine.bodies.get(a)!
    const cutGeometry = engine.regions.get(cut)!
    const start = { ...body.pos }
    const far = {
      x: cutGeometry.center.x + (cutGeometry.center.x - start.x),
      y: cutGeometry.center.y + (cutGeometry.center.y - start.y),
    }
    let maxPush = 0
    let observed = 0
    for (let frame = 0; frame <= 40; frame++) {
      const fraction = frame / 40
      const target = {
        x: start.x + (far.x - start.x) * fraction,
        y: start.y + (far.y - start.y) * fraction,
      }
      const clamped = clampDragToFeasible(engine, body, target)
      const distance = Math.hypot(clamped.x - cutGeometry.center.x, clamped.y - cutGeometry.center.y)
      expect(distance, `frame ${frame}: node centre must stay outside the cut circle`)
        .toBeGreaterThanOrEqual(cutGeometry.radius - 1e-6)
      maxPush = Math.max(maxPush, Math.hypot(clamped.x - target.x, clamped.y - target.y))
      observed++
    }
    expect(observed).toBe(41)
    expect(maxPush, 'the clamp engaged').toBeGreaterThan(cutGeometry.radius)
  })
})
