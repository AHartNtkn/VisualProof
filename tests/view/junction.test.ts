import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions, resolveOverlaps, establishFrame, applyContentScale, clampContentToFrame } from '../../src/view/relax'
import { paint, LIGHT } from '../../src/view/paint'
import { junctionShapes, junctionWids } from '../../src/view/junction'
import type { Vec2 } from '../../src/view/vec'

/** A synthetic asymmetric n-way junction: n refs wired at root through arg 0. */
function synth(n: number): ReturnType<typeof mkEngine> {
  const names = ['plus', 'times', 'succ', 'lt', 'eq', 'q']
  const bld = new DiagramBuilder()
  const refs = Array.from({ length: n }, (_, i) => bld.ref(bld.root, names[i % names.length]!, 2 + (i % 3)))
  bld.wire(bld.root, refs.map((node) => ({ node, port: { kind: 'arg' as const, index: 0 } })))
  const e = mkEngine(bld.build(), [])
  recomputeRegions(e); resolveOverlaps(e); establishFrame(e); applyContentScale(e); clampContentToFrame(e)
  return e
}

/** Every drawn junction-tributary sample point this frame. */
function junctionSamples(e: ReturnType<typeof mkEngine>): Vec2[] {
  const pts: Vec2[] = []
  for (const s of junctionShapes(e, LIGHT)) if (s.kind === 'polyline') for (const p of s.pts) pts.push(p)
  return pts
}

/** Directed Hausdorff distance from A to B (max over A of nearest point in B). */
function hausdorff(a: readonly Vec2[], b: readonly Vec2[]): number {
  let worst = 0
  for (const p of a) {
    let near = Infinity
    for (const q of b) near = Math.min(near, Math.hypot(p.x - q.x, p.y - q.y))
    worst = Math.max(worst, near)
  }
  return worst
}

describe('round-8 D junction rendering (promoted, USER-approved 2026-07-07)', () => {
  it('a ≥3-leg interior junction is drawn as tributaries, NOT a star of legs to one hub, and carries NO branch-point dot', () => {
    const e = synth(4)
    settle(e, 400)
    // the junction wire's star legs are NOT emitted as plain polylines by paint;
    // the tributary curves are, and there is no junction dot at the hub point.
    expect(junctionWids(e).size).toBe(1)
    const tribs = junctionShapes(e, LIGHT)
    expect(tribs.length, 'the junction emits tributary curves').toBeGreaterThanOrEqual(4)
    expect(tribs.every((s) => s.kind === 'polyline'), 'tributaries are curves, no dots').toBe(true)
    // full paint: no dot sits at the interior hub point (branch points are unmarked)
    const shapes = paint(e, LIGHT)
    const wire = e.wires.get([...junctionWids(e)][0]!)!
    const hub = wire.hub!
    const hubPos = hub.kind === 'point' ? hub.pos : e.bodies.get(hub.bodyId)!.pos
    const dotAtHub = shapes.some((s) => s.kind === 'dot' && Math.hypot(s.center.x - hubPos.x, s.center.y - hubPos.y) < 3 * e.scale)
    expect(dotAtHub, 'NO structural branch-point dot at the interior hub (USER 2026-07-07)').toBe(false)
  })

  it('NO SNAP: a slowly swept terminal moves the drawn tributaries smoothly (no frame-to-frame jump)', () => {
    const e = synth(4)
    settle(e, 400)
    junctionSamples(e) // warm the persistent tree to convergence
    // grab a ref body and sweep it slowly along a small arc; the drawn junction must
    // track continuously — the max frame-to-frame Hausdorff jump stays a small
    // multiple of the per-step body motion, never a snap to a re-derived shape.
    const ref = [...e.bodies.values()].find((b) => b.kind === 'ref')!
    const STEP = 0.5 // world units per frame — a slow sweep
    let prev = junctionSamples(e)
    let worst = 0
    for (let i = 0; i < 60; i++) {
      const a = (i / 60) * 0.6
      ref.pos = { x: ref.pos.x + Math.cos(a) * STEP, y: ref.pos.y + Math.sin(a) * STEP }
      // no full settle: this isolates the RENDER continuity, not the physics
      const cur = junctionSamples(e)
      worst = Math.max(worst, hausdorff(cur, prev), hausdorff(prev, cur))
      prev = cur
    }
    // a snap (topology flap / re-derivation) would jump many world-units at once; a
    // smooth track keeps the drawn shape within a few step-sizes of the last frame.
    expect(worst, `drawn junction jumped ${worst.toFixed(2)} wu in one frame (snap) — must track the ${STEP} wu/frame sweep`).toBeLessThan(4 * STEP)
  })
})
