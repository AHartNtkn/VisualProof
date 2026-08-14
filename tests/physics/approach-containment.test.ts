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

/** Deepest circle-circle penetration between drawn cuts where neither contains
    the other (ancestor pairs nest by construction; every other pair of cut
    circles must be disjoint — an intersection CHANGES WHAT THE DIAGRAM MEANS). */
function worstCutIntersection(e: Engine): number {
  const parentOf = (rid: RegionId): RegionId | null => {
    const reg = e.d.regions[rid]!
    return reg.kind === 'sheet' ? null : reg.parent
  }
  const isAncestor = (a: RegionId, b: RegionId): boolean => {
    for (let r = parentOf(b); r !== null; r = parentOf(r)) if (r === a) return true
    return false
  }
  const drawn = [...e.regions.keys()].filter((rid) => e.d.regions[rid]!.kind !== 'sheet')
  let worst = -Infinity
  for (let i = 0; i < drawn.length; i++) {
    for (let j = i + 1; j < drawn.length; j++) {
      const aId = drawn[i]!, bId = drawn[j]!
      if (isAncestor(aId, bId) || isAncestor(bId, aId)) continue
      const a = e.regions.get(aId)!, b = e.regions.get(bId)!
      const dist = Math.hypot(a.center.x - b.center.x, a.center.y - b.center.y)
      worst = Math.max(worst, a.radius + b.radius - dist)
    }
  }
  return worst
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

  it('a cut approaching a best on the far side of a sibling cut stays DISJOINT from it', () => {
    const b = new DiagramBuilder()
    const cutA = b.cut(b.root)
    b.ref(cutA, 'A', UNARY)
    b.ref(cutA, 'B', UNARY)
    const cutB = b.cut(b.root)
    b.ref(cutB, 'C', UNARY)
    b.ref(b.root, 'D', UNARY)
    const e = mkEngine(b.build(), [])
    // Every ref also carries a wire-owned dot body in its region, so regions
    // are seeded WHOLE: each region's bodies in a compact grid around its
    // intended centre. Cut A (two nodes + dots, so its derived circle has real
    // extent) starts due WEST of the single-node cut B; the root nodes sit far
    // north-east, widening the fixed frame so the journey and a corridor
    // around B both fit inside it.
    const byRegion = new Map<RegionId, string[]>()
    for (const [id, body] of e.bodies) {
      const list = byRegion.get(body.region) ?? []
      list.push(id)
      byRegion.set(body.region, list)
    }
    const place = (ids: readonly string[], cx: number, cy: number): void => {
      const rows = Math.ceil(ids.length / 2)
      ids.forEach((id, i) => {
        const col = i % 2, row = Math.floor(i / 2)
        e.bodies.get(id)!.pos = {
          x: cx + (ids.length === 1 ? 0 : col === 0 ? -9 : 9),
          y: cy + (row - (rows - 1) / 2) * 18,
        }
      })
    }
    place(byRegion.get(cutA)!, -55, 0)
    place(byRegion.get(cutB)!, 0, 0)
    place(byRegion.get(e.d.root)!, 70, 45)
    recomputeRegions(e)
    seedProject(e)
    recomputeRegions(e)

    const gA0 = e.regions.get(cutA)!
    const gB0 = e.regions.get(cutB)!
    const f = e.frame!
    // cut A must be able to pass AROUND cut B: room for its whole circle
    // between B's circle and the frame wall on at least one side
    const passNeed = gB0.radius + 2 * gA0.radius
    expect(
      f.half - Math.abs(gB0.center.y - f.center.y) - passNeed,
      'fixture sanity: a legal corridor around the sibling cut exists inside the frame',
    ).toBeGreaterThan(2)

    // the best puts cut A fully EAST of cut B (mirrored across it, pulled in
    // if the frame is tighter than the mirror), so the straight approach would
    // sweep A's circle through B's
    const targetCx = Math.min(
      2 * gB0.center.x - gA0.center.x,
      f.center.x + f.half - gA0.radius - 3,
    )
    expect(
      targetCx - gB0.center.x,
      'fixture sanity: the best pose puts cut A fully clear of cut B',
    ).toBeGreaterThan(gA0.radius + gB0.radius + 2)
    const shift = { x: targetCx - gA0.center.x, y: gB0.center.y - gA0.center.y }
    for (const id of byRegion.get(e.d.root)!) {
      const rb = e.bodies.get(id)!
      expect(
        Math.hypot(rb.pos.x - targetCx, rb.pos.y - gB0.center.y)
          - (gA0.radius + rb.discR * e.scale),
        'fixture sanity: the best pose keeps cut A clear of the root nodes',
      ).toBeGreaterThan(2)
    }

    const live = layoutScore(e)
    const snap = layoutSnapshot(e, 0)
    const poses = new Map([...snap.poses].map(([id, p]) => [id, { pos: { ...p.pos }, theta: p.theta }]))
    const targets = new Map<string, { x: number; y: number }>()
    for (const id of byRegion.get(cutA)!) {
      const p = poses.get(id)!
      const t = { x: p.pos.x + shift.x, y: p.pos.y + shift.y }
      targets.set(id, t)
      poses.set(id, { pos: t, theta: p.theta })
    }
    const best: LayoutBest = { score: live * 0.5 - 1, poses, nets: snap.nets }
    const search: LayoutSearch = {
      sync: () => {},
      best: () => best,
      adoptLive: () => {},
      searching: true,
    }
    attachLayoutSearch(e, search)

    let worst = -Infinity
    for (let i = 0; i < 2500; i++) {
      settleStep(e)
      worst = Math.max(worst, worstCutIntersection(e))
      const reached = [...targets].every(([id, t]) => {
        const p = e.bodies.get(id)!.pos
        return Math.hypot(p.x - t.x, p.y - t.y) < 0.5
      })
      if (reached) break
    }

    expect(
      worst,
      `two cut circles intersected ${worst.toFixed(2)} wu deep during the approach — semantics changed transiently`,
    ).toBeLessThanOrEqual(0)
    for (const [id, t] of targets) {
      const p = e.bodies.get(id)!.pos
      expect(
        Math.hypot(p.x - t.x, p.y - t.y),
        'the approach must still REACH the best — around the sibling cut, not through it',
      ).toBeLessThan(2)
    }
  })
})
