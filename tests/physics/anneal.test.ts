import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { Engine } from '../../src/view/engine'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions } from '../../src/view/relax'
import { layoutScore, LayoutOptimizer, applyLayoutSnapshot, MOVE_REGISTRY, movableUnits } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'

/**
 * THE ANNEALER (plan Task 4). Three contracts:
 *  1. ACCEPTANCE — a cut whose subtree is wedged between two wired nodes is
 *     moved aside; the old enumerated searcher (single-body hop + pair swap)
 *     cannot express that coordinated subtree displacement and stays trapped
 *     (observed at ratio 1.000), the annealer's `displaceSubtree` escapes.
 *  2. DETERMINISM — same seed ⇒ identical published-best sequence; a different
 *     seed ⇒ a different sequence (the search is a pure function of its seed).
 *  3. MOVE COVERAGE — every movable unit of a nested scene is covered by some
 *     registered move; adding a unit kind without a mover fails the test.
 */

/** Cut holding K star-wired refs (a heavy cohesive obstacle subtree — no
    wandering end dots), wedged between two wired root refs. */
function buildTrap(k: number): { d: Diagram; cut: string; n0: string; n1: string } {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const inner: string[] = []
  for (let i = 0; i < k; i++) inner.push(b.ref(cut, `C${i}`, relSig([TERM])))
  if (k >= 2) b.wire(cut, inner.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })), TERM)
  const n0 = b.ref(b.root, 'R', relSig([TERM]))
  const n1 = b.ref(b.root, 'S', relSig([TERM]))
  b.wire(b.root, [{ node: n0, port: { kind: 'arg', index: 0 } }, { node: n1, port: { kind: 'arg', index: 0 } }], TERM)
  return { d: b.build(), cut, n0, n1 }
}

/** The wedged local minimum: refs pushed apart on the x-axis, the cut blob
    clustered at the origin between them, then settled to rest. */
function trappedEngine(d: Diagram, cut: string, n0: string, n1: string): Engine {
  const e = mkEngine(d, [])
  const cutBodies = [...e.bodies.values()].filter((b) => b.region === cut)
  e.bodies.get(n0)!.pos = { x: -34, y: 0 }
  e.bodies.get(n1)!.pos = { x: 34, y: 0 }
  cutBodies.forEach((b, i) => { b.pos = { x: Math.cos(i * 2.4) * 5, y: Math.sin(i * 2.4) * 5 } })
  settle(e, 8000)
  recomputeRegions(e)
  return e
}

/** The cut circle diameter when `best` is laid out on a fresh engine. */
function cutDiameterOf(best: LayoutBest, d: Diagram, cut: string): number {
  const g = mkEngine(d, [])
  applyLayoutSnapshot(g, best)
  recomputeRegions(g)
  return 2 * g.regions.get(cut)!.radius
}

/** Drive the annealer directly for a bounded wall budget, returning the best. */
function anneal(e: Engine, seed: number, budgetMs: number): LayoutBest {
  const opt = new LayoutOptimizer(seed)
  opt.sync(e, null)
  const t0 = performance.now()
  while (performance.now() - t0 < budgetMs) opt.tick(null, 200)
  return opt.best()!
}

/** The published-best score after each of `epochs` single-epoch ticks. */
function bestSequence(e: Engine, seed: number, epochs: number): number[] {
  const opt = new LayoutOptimizer(seed)
  opt.sync(e, null)
  const seq: number[] = []
  for (let k = 0; k < epochs; k++) { opt.tick(null, 0); seq.push(opt.best()!.score) }
  return seq
}

describe('annealer escapes the wedged-cut trap (plan Task 4 acceptance)', () => {
  it('a cut subtree wedged between two wired refs is moved aside; best <= 0.6x trapped', () => {
    const { d, cut, n0, n1 } = buildTrap(4)
    const e = trappedEngine(d, cut, n0, n1)
    const trapped = layoutScore(e)

    // The brief specifies a 60 s budget; the physics suite caps a test at 30 s
    // (never to be raised), so the wall budget is 15 s. The annealer reaches the
    // escaped basin in ~6 s here (measured), so 15 s leaves >2x margin while the
    // whole test stays ~17 s, well under the cap.
    const best = anneal(e, 0xace4, 15000)

    const b0 = best.poses.get(n0)!.pos, b1 = best.poses.get(n1)!.pos
    const refDist = Math.hypot(b0.x - b1.x, b0.y - b1.y)
    const cutDiam = cutDiameterOf(best, d, cut)

    expect(best.score, `best ${best.score.toFixed(1)} vs 0.6·trapped ${(0.6 * trapped).toFixed(1)}`)
      .toBeLessThanOrEqual(0.6 * trapped)
    expect(refDist, `two wired refs ${refDist.toFixed(1)} vs cut diameter ${cutDiam.toFixed(1)}`)
      .toBeLessThan(cutDiam)
  })
})

describe('the annealed search is deterministic in its seed (plan Task 4)', () => {
  it('same seed ⇒ identical best sequence; a different seed ⇒ a different one', () => {
    // a small trap (fast polish) that still has seed-dependent escape basins
    const { d, cut, n0, n1 } = buildTrap(2)
    const e = trappedEngine(d, cut, n0, n1) // built once; the annealer reads, never mutates it

    const a1 = bestSequence(e, 0xace4, 3)
    const a2 = bestSequence(e, 0xace4, 3)
    const b = bestSequence(e, 0x00a1, 3)

    expect(a1, 'same seed must reproduce the published-best sequence bit-for-bit').toEqual(a2)
    expect(a1, 'a different seed must explore a different trajectory').not.toEqual(b)
  })
})

describe('every movable unit has a covering move (plan Task 4 coverage)', () => {
  it('the move registry covers each body, region subtree, and wire-owned end dot', () => {
    // a nested scene: a cut holding an atom (its dangling ports become wire-owned
    // end dots), plus a root ref — every unit taxon is present.
    const b = new DiagramBuilder()
    const inner = b.cut(b.root)
    b.atom(inner, relSig([TERM]))
    b.ref(b.root, 'R', relSig([TERM]))
    const e = mkEngine(b.build(), [])
    recomputeRegions(e)

    const units = movableUnits(e)
    // the fixture must actually exercise all three taxa, or the test is vacuous
    expect(units.some((u) => u.kind === 'body'), 'fixture has body units').toBe(true)
    expect(units.some((u) => u.kind === 'region'), 'fixture has region units').toBe(true)
    expect(units.some((u) => u.kind === 'endDot'), 'fixture has wire-owned end-dot units').toBe(true)

    for (const u of units) {
      const covered = MOVE_REGISTRY.some((m) => m.covers(u))
      expect(covered, `movable unit ${JSON.stringify(u)} has no covering move`).toBe(true)
    }
  })
})
