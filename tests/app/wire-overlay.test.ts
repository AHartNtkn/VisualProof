import { describe, expect, it } from 'vitest'
import { ConnectionDragController } from '../../src/app/interact/connection'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import type { Engine } from '../../src/view/engine'
import { mkEngine } from '../../src/view/engine'
import { establishFrame, recomputeRegions, resolveOverlaps, settleStep } from '../../src/view/relax'
import { LIGHT, wireOverlayShapes } from '../../src/view/paint'
import { legPaths } from '../../src/view/wires'
import type { Vec2 } from '../../src/view/vec'

/**
 * WIRE OVERLAYS RESTROKE THE PAINTED CURVE (USER 2026-07-30: highlighting a
 * term wire shows "a discretization" — the overlay drew the 7-samples-per-
 * cubic polyline while the painter draws true Bézier cubics; relation wires
 * looked right only because their hover goes through highlightGroup, a
 * SECOND implementation that already restrokes cubics).
 *
 * The law: every hover/selection/drag overlay of a wire draws the SAME Hobby
 * cubic chain the painter draws — one shared geometry, styled per context.
 * Never a resampled polyline.
 */

const UNARY = relSig([IOTA])

/** Two separate 2-ref term wires plus one 2-atom relational wire. */
function scene(): { e: Engine; term: string; rel: string } {
  const b = new DiagramBuilder()
  const r0 = b.ref(b.root, 'A', UNARY)
  const r1 = b.ref(b.root, 'B', UNARY)
  const term = b.wire(b.root, [
    { node: r0, port: { kind: 'arg', index: 0 } },
    { node: r1, port: { kind: 'arg', index: 0 } },
  ])
  const a0 = b.atom(b.root, UNARY)
  const a1 = b.atom(b.root, UNARY)
  const rel = b.wire(b.root, [
    { node: a0, port: { kind: 'head' } },
    { node: a1, port: { kind: 'head' } },
  ], UNARY)
  const e = mkEngine(b.build(), [])
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e)
  for (let t = 0; t < 60; t++) if (!settleStep(e)) break
  recomputeRegions(e)
  return { e, term, rel }
}

/** The painted cubic chains of one wire, in leg order. */
const paintedCubics = (e: Engine, wid: string): unknown[] =>
  legPaths(e).filter((l) => l.wid === wid).map((l) => l.cubics)

describe('wire overlays are the painted cubics, never a polyline', () => {
  it('wireOverlayShapes restrokes the painter geometry for term AND relation wires', () => {
    const { e, term, rel } = scene()
    for (const wid of [term, rel]) {
      const shapes = wireOverlayShapes(e, wid, '#f00', 3)
      const strokes = shapes.filter((s) => s.kind === 'bezierPath')
      expect(shapes.some((s) => s.kind === 'polyline'), `${wid}: overlay contains a resampled polyline`).toBe(false)
      expect(strokes.length, `${wid}: overlay restrokes every painted leg`).toBe(paintedCubics(e, wid).length)
      expect(strokes.map((s) => (s.kind === 'bezierPath' ? s.cubics : null)), `${wid}: overlay cubics ARE the painted cubics`)
        .toEqual(paintedCubics(e, wid))
    }
  })

  it('the connection drag target overlay restrokes the painted cubics', () => {
    const { e, term } = scene()
    const mk = (point: Vec2): PointerSample => ({
      pointerId: 1, button: 0, client: point, screen: point, world: point,
      hit: null, shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    })
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => e,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: () => true,
      refuse: () => undefined,
    })
    // grab the relational wire mid-stroke, hover the term wire mid-stroke
    const mid = (wid: string): Vec2 => {
      const pts = legPaths(e).find((l) => l.wid === wid)!.pts
      return pts[Math.floor(pts.length / 2)]!
    }
    const { rel } = { rel: [...e.wires.keys()].find((w) => w !== term)! }
    const claim = drag.claim(mk(mid(rel)))
    expect(claim, 'sanity: the drag claims the grabbed wire').not.toBeNull()
    claim!.move(mk(mid(term)))

    const overlay = drag.overlay()
    expect(overlay.length, 'sanity: the drag renders a target overlay').toBeGreaterThan(1)
    expect(overlay.some((s) => s.kind === 'polyline'), 'drag overlay contains a resampled polyline').toBe(false)
    const strokes = overlay.filter((s) => s.kind === 'bezierPath')
    expect(strokes.map((s) => (s.kind === 'bezierPath' ? s.cubics : null)), 'drag target overlay cubics ARE the painted cubics')
      .toEqual(paintedCubics(e, term))
  })
})
