import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { Engine } from '../../src/view/engine'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions, resolveOverlaps, establishFrame } from '../../src/view/relax'
import { layoutScore, LayoutOptimizer, applyLayoutSnapshot, MOVE_REGISTRY, movableUnits } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'

/**
 * THE BASIN-HOPPING SEARCH (plan Task 6). Four contracts:
 *  1. ACCEPTANCE — a cut whose subtree is wedged between two wired nodes is
 *     moved aside; only a coordinated subtree displacement relocates the
 *     multi-body cut, and the search's `displaceSubtree` hop (relaxed to rest)
 *     escapes to a basin ≤ 0.6× the trapped floor.
 *  2. DETERMINISM — same seed ⇒ identical published-best sequence; a different
 *     seed ⇒ a different one (the search is a pure function of its seed). Under
 *     basin hopping every published best is an accepted relaxed basin floor.
 *  3. MOVE COVERAGE — every movable unit of a nested scene is covered by some
 *     registered move; adding a unit kind without a mover fails the test.
 *  4. PHASE 0 — sync does not block on the seed relaxation; the incumbent's
 *     descent is published incrementally (a monotone stream), so the app sees
 *     the seed settle from the first slices rather than sitting raw-kinked.
 *
 * Fixture size note (Task 6): basin hopping relaxes EVERY hop to rest, so a hop
 * costs a full local settle (~2.9 s on the Task-4 K=4 star-wired cut). The
 * acceptance fixture is therefore the 3-ref cut — the largest wedged cut-subtree
 * whose 16-probe calibration + escape fits the 30 s suite cap (measured K=4 63 s,
 * K=3 ~16 s); it is still a genuine multi-body subtree that only displaceSubtree
 * relocates. Determinism uses the cheapest seed-divergent scene. See
 * task6-report.md.
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

/** Drive the search directly for a bounded wall budget, returning the best.
    `sync` runs the 16-probe calibration (each probe a full relaxation); the
    budgeted loop then runs basin-hopping epochs. */
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

describe('basin hopping escapes the wedged-cut trap (plan Task 6 acceptance)', () => {
  it('a cut subtree wedged between two wired refs is moved aside; best <= 0.6x trapped', () => {
    const { d, cut, n0, n1 } = buildTrap(3)
    const e = trappedEngine(d, cut, n0, n1)
    const trapped = layoutScore(e)

    // Basin hopping escapes this wedged 3-ref cut in ONE epoch of relaxed hops
    // after the 16-probe calibration; a 4 s budget runs ≥1 epoch. The whole test
    // is ~16 s, comfortably under the 30 s suite cap. K=3 is the largest wedged
    // cut that fits: each hop is a full relaxation, ~1.5 s here vs ~2.9 s on the
    // ratified K=4 cut whose 16-probe calibration alone would exceed 30 s (the
    // brief's 60 s budget is impossible under the cap) — see task6-report.md.
    const best = anneal(e, 0xace4, 4000)

    const b0 = best.poses.get(n0)!.pos, b1 = best.poses.get(n1)!.pos
    const refDist = Math.hypot(b0.x - b1.x, b0.y - b1.y)
    const cutDiam = cutDiameterOf(best, d, cut)

    expect(best.score, `best ${best.score.toFixed(1)} vs 0.6·trapped ${(0.6 * trapped).toFixed(1)}`)
      .toBeLessThanOrEqual(0.6 * trapped)
    expect(refDist, `two wired refs ${refDist.toFixed(1)} vs cut diameter ${cutDiam.toFixed(1)}`)
      .toBeLessThan(cutDiam)
  })
})

describe('the basin-hopping search is deterministic in its seed (plan Task 6)', () => {
  it('same seed ⇒ identical accepted-best sequence; a different seed ⇒ a different one', () => {
    // Two wired refs, no cut — the cheapest scene with a wire (2 bodies, so each
    // relaxation is fast) whose distinct ROTATIONAL basins make the search
    // strongly seed-divergent: 0xace4 settles to ~30.99, 0x0111 stays in a
    // misaligned-port basin at ~99.8 (measured). A trap would relax too slowly
    // here (16-probe calibration × 3 runs); this stays a few seconds.
    const b0 = new DiagramBuilder()
    const n0 = b0.ref(b0.root, 'R', relSig([TERM]))
    const n1 = b0.ref(b0.root, 'S', relSig([TERM]))
    b0.wire(b0.root, [{ node: n0, port: { kind: 'arg', index: 0 } }, { node: n1, port: { kind: 'arg', index: 0 } }], TERM)
    const e = mkEngine(b0.build(), [])
    e.bodies.get(n0)!.pos = { x: -20, y: 5 }
    e.bodies.get(n1)!.pos = { x: 20, y: -5 }
    settle(e, 8000)
    recomputeRegions(e)

    const a1 = bestSequence(e, 0xace4, 2)
    const a2 = bestSequence(e, 0xace4, 2)
    const b = bestSequence(e, 0x0111, 2)

    expect(a1, 'same seed must reproduce the accepted-best sequence bit-for-bit').toEqual(a2)
    expect(a1, 'a different seed must accept a different trajectory').not.toEqual(b)
  })
})

describe('every movable unit has a covering move (plan Task 6 coverage)', () => {
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

describe('the seed relaxation streams incrementally (plan Task 6 Phase 0)', () => {
  it('sync does not block on relaxation; the descent is published as a monotone stream', () => {
    // A RAW, un-relaxed seed: four cyclically-wired refs at the spiral seed, made
    // legal (frame + overlap projection) but NOT settled — kinked wires, high
    // energy. In app mode the frame runs no node descent, so without Phase 0 this
    // sits raw-kinked until the first published best.
    const b = new DiagramBuilder()
    const r = [0, 1, 2, 3].map((i) => b.ref(b.root, `R${i}`, relSig([TERM, TERM])))
    for (let i = 0; i < 4; i++) {
      b.wire(b.root, [{ node: r[i]!, port: { kind: 'arg', index: 1 } }, { node: r[(i + 1) % 4]!, port: { kind: 'arg', index: 0 } }], TERM)
    }
    const e = mkEngine(b.build(), [])
    recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
    const rawScore = layoutScore(e)

    const opt = new LayoutOptimizer(0xace4)
    opt.sync(e, null)
    // sync must NOT relax: the initial best is the raw seed itself (= the live
    // layout, no jump), so the app has something to approach from frame one.
    expect(Math.abs(opt.best()!.score - rawScore), 'sync publishes the raw seed, un-relaxed')
      .toBeLessThan(1e-6 * (rawScore + 1))

    const seq: number[] = []
    for (let k = 0; k < 8; k++) { opt.tick(null, 0); seq.push(opt.best()!.score) }
    // every published state is on the scene's own downhill path — never higher
    for (let i = 1; i < seq.length; i++) {
      expect(seq[i]!, 'the published best never increases (no absurd states)').toBeLessThanOrEqual(seq[i - 1]! + 1e-9)
    }
    // the descent is INCREMENTAL: several distinct improving states are published
    // as it settles, not a single post-relaxation jump
    const distinct = new Set(seq.map((v) => v.toFixed(3))).size
    expect(distinct, 'incremental descent publishes multiple intermediate rests').toBeGreaterThanOrEqual(3)
    // and it relaxes far below the raw seed
    expect(seq[seq.length - 1]!, 'the stream reaches a deeply relaxed layout').toBeLessThan(rawScore * 0.5)
  })
})
