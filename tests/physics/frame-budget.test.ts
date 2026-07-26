import { describe, it, expect } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { settleStep, recomputeRegions, resolveOverlaps, attachLayoutSearch, WIREP } from '../../src/view/relax'
import type { LayoutSearch } from '../../src/view/relax'
import { layoutSnapshot } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'
import { identityJunctionScene, identityRefScene } from '../fixtures/zero-signature'

/**
 * THE FRAME CONTRACT (USER ruling 2026-07-24): layout minimization is
 * asynchronous — "the user should not perceive anything from a heavy
 * search". A frame on an engine with a LayoutSearch attached does only
 * bounded work: push state, one bounded approach step, the wire walk.
 * It NEVER runs the local node descent (that is the searcher's job,
 * off-thread). Measured before this contract: 650–2700 ms per frame on
 * these fixtures — the reported "insanely laggy" app.
 */

/** A real, minimal search: knows nothing, stays searching. An engine with
    this attached must still produce cheap frames — the frame's cost cannot
    depend on what the searcher has found. */
const emptySearch = (): LayoutSearch => ({
  sync: () => {},
  best: () => null,
  adoptLive: () => {},
  searching: true,
})

function fixtureEngine(name: 'identity-ref' | 'identity-junction'): Engine {
  const diagram = name === 'identity-ref' ? identityRefScene() : identityJunctionScene()
  const e = mkEngine(diagram, [])
  recomputeRegions(e)
  resolveOverlaps(e)
  return e
}

describe('searched frames are light (async-search law)', () => {
  it('settleStep with a search attached never runs heavy minimization', () => {
    const e = fixtureEngine('identity-junction')
    attachLayoutSearch(e, emptySearch())
    // first frame includes frame establishment + a full walk transition
    const t0 = performance.now()
    settleStep(e)
    const first = performance.now() - t0
    let total = 0
    for (let i = 0; i < 30; i++) {
      const s = performance.now()
      settleStep(e)
      total += performance.now() - s
    }
    const mean = total / 30
    // local-solver frames measured 2100+ ms here; the searched frame must be
    // an order of magnitude under that even on slow CI
    expect(first).toBeLessThan(1000)
    expect(mean).toBeLessThan(150)
  })

  it('bodies never move without a better best; with one they approach boundedly', () => {
    const e = fixtureEngine('identity-ref')
    let best: LayoutBest | null = null
    const search: LayoutSearch = {
      sync: () => {},
      best: () => best,
      adoptLive: () => {},
      searching: true,
    }
    attachLayoutSearch(e, search)
    settleStep(e) // establish frame; walk may move wires
    const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
    for (let i = 0; i < 5; i++) settleStep(e)
    for (const [id, b] of e.bodies) {
      const p = before.get(id)!
      expect(Math.hypot(b.pos.x - p.x, b.pos.y - p.y), `body ${id} moved with no best`).toBe(0)
    }

    // now hand the search a strictly-better best displaced from live: bodies
    // must move toward it, at most travelCap·scale per frame
    const target = layoutSnapshot(e, -1e9)
    const shifted = new Map([...target.poses].map(([id, p]) => [id, { pos: { x: p.pos.x + 40, y: p.pos.y }, theta: p.theta }]))
    best = { score: -1e9, poses: shifted, nets: target.nets }
    const bound = WIREP.travelCap * e.scale + 1e-9
    const prev = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
    settleStep(e)
    let moved = 0
    for (const [id, b] of e.bodies) {
      const p = prev.get(id)!
      const d = Math.hypot(b.pos.x - p.x, b.pos.y - p.y)
      expect(d, `body ${id} exceeded the approach bound`).toBeLessThanOrEqual(bound)
      moved = Math.max(moved, d)
    }
    expect(moved).toBeGreaterThan(0)
  })
})
