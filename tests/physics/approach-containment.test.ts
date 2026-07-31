import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { RegionId } from '../../src/kernel/diagram/diagram'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { attachLayoutSearch, recomputeRegions, seedProject, settleStep } from '../../src/view/relax'
import type { LayoutSearch } from '../../src/view/relax'
import { layoutScore, layoutSnapshot } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'
import { UNARY } from '../fixtures/zero-signature'

/**
 * HARD SEMANTIC CONTAINMENT HOLDS DURING THE PRESENTATION APPROACH (USER
 * 2026-07-30, restating the 2026-07-06 law): a node crossing a cut it is not
 * part of CHANGES WHAT THE DIAGRAM MEANS, so it must not happen even
 * transiently — drags are already clamped (`clampDragToFeasible`), and the
 * smooth animation toward a searched best is subject to the SAME law. The
 * approach must take nodes AROUND foreign cuts, exactly as a drag would.
 */

/** Non-ancestor cut circles the body must stay clear of. */
function foreignCuts(e: Engine, region: RegionId): RegionId[] {
  const ancestors = new Set<RegionId>()
  for (let r = region; ;) {
    ancestors.add(r)
    const reg = e.d.regions[r]!
    if (reg.kind === 'sheet') break
    r = reg.parent
  }
  return [...e.regions.keys()].filter((rid) => !ancestors.has(rid) && e.d.regions[rid]!.kind !== 'sheet')
}

describe('the presentation approach never violates semantic containment', () => {
  it('a node approaching a best on the far side of a foreign cut goes AROUND it', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    b.ref(cut, 'C', UNARY)
    const mover = b.ref(b.root, 'A', UNARY)
    const anchor = b.ref(b.root, 'B', UNARY)
    const e = mkEngine(b.build(), [])
    // spread the seed WIDE before the frame is established, so the fixed
    // frame encloses the whole journey and a legal corridor around the cut
    // exists — an unreachable best is a different (legitimate) situation
    for (const [id, body] of e.bodies) {
      if (id === mover) body.pos = { x: -55, y: 0 }
      else if (id === anchor) body.pos = { x: 55, y: 0 }
      else if (body.region === cut) body.pos = { x: 0, y: 0 }
    }
    recomputeRegions(e)
    seedProject(e)
    recomputeRegions(e)

    // the mover sits due WEST of the cut, its best due EAST: the straight
    // path runs through the cut circle's centre
    const g0 = e.regions.get(cut)!
    const bm = e.bodies.get(mover)!
    const need = bm.discR * e.scale + g0.radius + 5 * e.scale
    const f = e.frame!
    expect(
      f.half - Math.abs(g0.center.y - f.center.y) - need,
      'fixture sanity: a legal corridor around the cut exists inside the frame',
    ).toBeGreaterThan(2)
    const away = need + 6
    const target = { x: g0.center.x + away, y: g0.center.y }
    expect(Math.abs(target.x - f.center.x), 'fixture sanity: the best pose is inside the frame')
      .toBeLessThan(f.half - bm.discR * e.scale)
    const live = layoutScore(e)
    const poses = new Map([...layoutSnapshot(e, 0).poses].map(([id, p]) => [id, { pos: { ...p.pos }, theta: p.theta }]))
    poses.set(mover, { pos: target, theta: bm.theta })
    const best: LayoutBest = { score: live * 0.5, poses, nets: layoutSnapshot(e, 0).nets }

    const search: LayoutSearch = {
      sync: () => {},
      best: () => best,
      adoptLive: () => {},
      searching: true,
    }
    attachLayoutSearch(e, search)

    let worst = 0
    for (let i = 0; i < 2500; i++) {
      settleStep(e)
      for (const body of e.bodies.values()) {
        for (const rid of foreignCuts(e, body.region)) {
          const g = e.regions.get(rid)!
          const inside = g.radius - Math.hypot(body.pos.x - g.center.x, body.pos.y - g.center.y)
          worst = Math.max(worst, inside)
        }
      }
      const m = e.bodies.get(mover)!.pos
      if (Math.hypot(m.x - target.x, m.y - target.y) < 0.5) break
    }

    expect(
      worst,
      `a node entered a foreign cut ${worst.toFixed(2)} wu deep during the approach — semantics changed transiently`,
    ).toBeLessThanOrEqual(0)
    const m = e.bodies.get(mover)!.pos
    expect(
      Math.hypot(m.x - target.x, m.y - target.y),
      'the approach must still REACH the best — around the cut, not through it',
    ).toBeLessThan(2)
  })
})
