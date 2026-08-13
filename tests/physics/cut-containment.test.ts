import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import type { RegionId } from '../../src/kernel/diagram/diagram'
import { establishFrame, recomputeRegions, settleStep } from '../../src/view/relax'
import { legPaths } from '../../src/view/wires'
import type { Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

/**
 * SEMANTIC CUT CONTAINMENT FOR WIRES.
 *
 * A cut is a scope boundary: a stroke that visibly enters and leaves a cut
 * reads as crossing into that cut. A wire with no terminal inside a cut (and
 * no terminal in any of its descendants) is NEVER inside it, so its drawn
 * stroke must not run through the drawn circle — the reader cannot tell an
 * accidental fly-through from a real crossing.
 *
 * Node containment is HARD (projection + drag clamp). For WIRES nothing may
 * be banned outright (USER 2026-07-24: "no explicit bans on any
 * configuration, period" — everything goes on the energy), so the law
 * asserted here is BEHAVIORAL: at rest the stroke does not run through a cut
 * it is not in. The energy must make the detour cheaper than the fly-through.
 */

/** Length of segment ab inside the circle (c, R) — chord clipping. */
function segInsideLen(a: Vec2, b: Vec2, c: Vec2, R: number): number {
  const dx = b.x - a.x, dy = b.y - a.y
  const L = Math.hypot(dx, dy)
  if (L < 1e-12) return 0
  const fx = a.x - c.x, fy = a.y - c.y
  const bq = (fx * dx + fy * dy) / L
  const cc = fx * fx + fy * fy - R * R
  const disc = bq * bq - cc
  if (disc <= 0) return 0
  const sq = Math.sqrt(disc)
  const t0 = Math.max(0, -bq - sq), t1 = Math.min(L, -bq + sq)
  return Math.max(0, t1 - t0)
}

/** Drawn length of one wire inside one region's drawn circle. */
function wireLengthInsideRegion(e: Engine, wid: string, rid: RegionId): number {
  const g = e.regions.get(rid)!
  let inside = 0
  for (const p of legPaths(e)) {
    if (p.wid !== wid) continue
    for (let i = 0; i + 1 < p.pts.length; i++) inside += segInsideLen(p.pts[i]!, p.pts[i + 1]!, g.center, g.radius)
  }
  return inside
}

describe('a wire never runs through a cut it is not inside', () => {
  it('routes AROUND an empty cut standing between its two pinned nodes', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const left = b.ref(b.root, 'L', UNARY)
    const right = b.ref(b.root, 'R', UNARY)
    const w = b.wire([
      { node: left, port: { kind: 'arg', index: 0 } },
      { node: right, port: { kind: 'arg', index: 0 } },
    ])
    const e = mkEngine(b.build(), [])

    // The scene is FIXED by pinning: the cut sits exactly on the straight line
    // between the two wired nodes, so a straight stroke must run through the
    // drawn circle. With every body pinned, the only way the stroke can leave
    // the cut is for the ROUTE to detour — which only the wire energy can ask
    // for. This isolates the exact defect: the metric does not see cuts.
    const place = (id: string, at: Vec2): void => { e.bodies.get(id)!.pos = at }
    place(left, { x: -45, y: 0 })
    place(right, { x: 45, y: 0 })
    place(`anchor:${cut}`, { x: 0, y: 0 })
    const pinned = new Set([left, right, `anchor:${cut}`])
    recomputeRegions(e)
    establishFrame(e)

    const g = e.regions.get(cut)!
    expect(g.radius, 'the empty cut draws its minimum circle').toBeGreaterThan(5)
    expect(
      segInsideLen({ x: -45, y: 0 }, { x: 45, y: 0 }, g.center, g.radius),
      'the fixture puts the cut across the straight line between the nodes',
    ).toBeGreaterThan(2 * g.radius - 1)

    for (let t = 0; t < 600; t++) if (!settleStep(e, pinned)) break
    recomputeRegions(e)

    const inside = wireLengthInsideRegion(e, w, cut)
    expect(
      inside,
      `the wire is scoped on the sheet and has no terminal in the cut, yet ${inside.toFixed(2)} wu of its stroke runs through the cut circle`,
    ).toBeLessThan(1)
  })

})
