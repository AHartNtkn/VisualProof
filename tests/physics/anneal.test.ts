import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import type { Engine } from '../../src/view/engine'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions, resolveOverlaps, establishFrame } from '../../src/view/relax'
import { layoutScore, LayoutOptimizer, MOVE_REGISTRY, movableUnits } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'

/**
 * THE UNIFIED-CHAIN SEARCH (plan Task 6 contracts, re-derived for the
 * 2026-07-31 unified chain — one Metropolis chain over multi-scale
 * delta-priced moves; the deterministic solver survives as the streamed seed
 * polish and the publish-time rest certificate). Four contracts:
 *  1. ACCEPTANCE — a cut whose subtree is wedged between crossing wires is
 *     moved aside; only a coordinated subtree displacement relocates the
 *     multi-body cut, and the chain reaches the measured aside floor.
 *  2. DETERMINISM — same seed ⇒ identical published-best sequence; a different
 *     seed ⇒ a different one (the search is a pure function of its seed).
 *     Every published best past the streamed seed descent is a certified rest.
 *  3. MOVE COVERAGE — every movable unit of a nested scene is covered by some
 *     registered move; adding a unit kind without a mover fails the test.
 *  4. PHASE 0 — sync does not block on the seed relaxation; the incumbent's
 *     descent is published incrementally (a monotone stream), so the app sees
 *     the seed settle from the first slices rather than sitting raw-kinked.
 *
 * Fixture note: the 3-ref cut is a genuine multi-body subtree that only
 * displaceSubtree relocates; determinism uses the cheapest seed-divergent
 * scene.
 */

/** Cut holding K star-wired refs (a heavy cohesive obstacle subtree — no
    wandering end dots), wedged between `pairs` left–right wired ref pairs.
    Under the cut-obstacle metric (2026-07-30) a SINGLE crossing wire just
    detours around the wedge at modest cost — the wedge is not a trap — so the
    fixture crosses it with two wires: each pays its detour plus separation
    against the other's, and moving the cut aside wins decisively (measured
    trapped 1589.6 vs aside 377.3). */
function buildTrap(k: number, pairs: number): { d: Diagram; cut: string; left: string[]; right: string[] } {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const inner: string[] = []
  for (let i = 0; i < k; i++) inner.push(b.ref(cut, `C${i}`, relSig([IOTA])))
  if (k >= 2) {
    b.wire(inner.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })), IOTA)
  }
  const left: string[] = [], right: string[] = []
  for (let p = 0; p < pairs; p++) {
    const n0 = b.ref(b.root, `L${p}`, relSig([IOTA]))
    const n1 = b.ref(b.root, `R${p}`, relSig([IOTA]))
    b.wire( [{ node: n0, port: { kind: 'arg', index: 0 } }, { node: n1, port: { kind: 'arg', index: 0 } }], IOTA)
    left.push(n0); right.push(n1)
  }
  return { d: b.build(), cut, left, right }
}

/** A settled rest from an explicit seed: ref pairs spread on the x-axis, the
    cut blob either wedged at the origin between them or displaced aside. The
    aside rest is the acceptance REFERENCE floor — measured in-test, so the
    contract self-calibrates to the current energy instead of pinning a stale
    ratio. */
function settledSeed(t: { d: Diagram; cut: string; left: string[]; right: string[] }, aside: boolean): Engine {
  const e = mkEngine(t.d, [])
  const n = t.left.length
  t.left.forEach((id, p) => { e.bodies.get(id)!.pos = { x: -34, y: (p - (n - 1) / 2) * 16 } })
  t.right.forEach((id, p) => { e.bodies.get(id)!.pos = { x: 34, y: (p - (n - 1) / 2) * 16 } })
  ;[...e.bodies.values()].filter((b) => b.region === t.cut).forEach((b, i) => {
    b.pos = aside
      ? { x: Math.cos(i * 2.4) * 5, y: 45 + Math.sin(i * 2.4) * 5 }
      : { x: Math.cos(i * 2.4) * 5, y: Math.sin(i * 2.4) * 5 }
  })
  settle(e, 8000)
  recomputeRegions(e)
  return e
}

/** Drive the search one atomic unit per tick until the best reaches `target`
    or `maxUnits` is spent. `tick(null, 0)` advances exactly one unit (one
    streamed-descent quantum, one silent polish quantum, or one chain move) —
    the sliced granularity the worker uses so no single tick blocks. */
function anneal(e: Engine, seed: number, target: number, maxUnits: number): LayoutBest {
  const opt = new LayoutOptimizer(seed)
  opt.sync(e, null)
  for (let k = 0; k < maxUnits && opt.best()!.score > target; k++) opt.tick(null, 0)
  return opt.best()!
}

/** The published-best score after each of `units` single-unit ticks — the
    deterministic published sequence (phase-0 descent quanta, then, once past the
    16 calibration probes, accepted basin floors). */
function bestSequence(e: Engine, seed: number, units: number): number[] {
  const opt = new LayoutOptimizer(seed)
  opt.sync(e, null)
  const seq: number[] = []
  for (let k = 0; k < units; k++) { opt.tick(null, 0); seq.push(opt.best()!.score) }
  return seq
}

describe('the chain escapes the wedged-cut trap (plan Task 6 acceptance)', () => {
  it('a cut subtree wedged between two crossing wires is moved aside, reaching the measured aside floor', () => {
    const trap = buildTrap(3, 2)
    const e = settledSeed(trap, false)
    const trapped = layoutScore(e)
    const asideFloor = layoutScore(settledSeed(trap, true))

    // fixture sanity: the wedge IS a trap under the current energy — the aside
    // basin is far lower, and only a coordinated subtree displacement relocates
    // the multi-body cut (measured 2026-07-30: trapped 1589.6, aside 377.3).
    expect(asideFloor, `aside ${asideFloor.toFixed(1)} must undercut trapped ${trapped.toFixed(1)} decisively`)
      .toBeLessThan(0.5 * trapped)

    // Under the unified chain a UNIT is one delta-priced move (or one silent
    // polish quantum), not a full quench — the same escape now spans thousands
    // of cheap units instead of ~17 expensive ones. The target is the measured
    // aside floor itself (+2% relaxation slack): the search must actually find
    // the basin the reference seed settles into, not merely improve.
    const best = anneal(e, 0xace4, asideFloor * 1.02, 60000)

    expect(best.score, `best ${best.score.toFixed(1)} vs aside floor ${asideFloor.toFixed(1)} (trapped ${trapped.toFixed(1)})`)
      .toBeLessThanOrEqual(asideFloor * 1.02)
  })
})

describe('the chain is deterministic in its seed (plan Task 6)', () => {
  it('same seed ⇒ identical published sequence (phase-0 quanta included); a different seed ⇒ a different one', () => {
    // A RAW (un-settled) two-ref scene — the cheapest scene with a wire (2 bodies,
    // fast relaxations). The published sequence over single-unit ticks is: the
    // phase-0 descent quantum(s) (seed-INDEPENDENT — descent has no randomness),
    // then chain moves whose first certified improvement lands at a
    // SEED-DEPENDENT unit. Publishing on fixed unit quanta makes the sequence
    // a pure function of the seed, robust to how ticks slice wall-time.
    const rawTwoRef = (): Engine => {
      const b0 = new DiagramBuilder()
      const n0 = b0.ref(b0.root, 'R', relSig([IOTA]))
      const n1 = b0.ref(b0.root, 'S', relSig([IOTA]))
      b0.wire( [{ node: n0, port: { kind: 'arg', index: 0 } }, { node: n1, port: { kind: 'arg', index: 0 } }], IOTA)
      const e = mkEngine(b0.build(), [])
      e.bodies.get(n0)!.pos = { x: -20, y: 5 }
      e.bodies.get(n1)!.pos = { x: 20, y: -5 }
      recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
      return e
    }
    // units are chain moves now (ms-scale): run enough for the seeded chains
    // to publish their first seed-dependent improvements
    const a1 = bestSequence(rawTwoRef(), 0xace4, 2500)
    const a2 = bestSequence(rawTwoRef(), 0xace4, 2500)
    const b = bestSequence(rawTwoRef(), 0x0111, 2500)

    expect(a1, 'same seed must reproduce the published sequence bit-for-bit').toEqual(a2)
    expect(a1, 'a different seed must produce a different sequence').not.toEqual(b)
  })
})

describe('every movable unit has a covering move (plan Task 6 coverage)', () => {
  // NEEDS-ADJUDICATION: this asserts a scene exercises the `endDot` movable-unit
  // taxon, which mkEngine can no longer produce — the engine synthesizes no
  // wire-owned end bodies (`WireView.end` is always null now that every wire end
  // is a real pin node), so `movableUnits` never emits an endDot for any diagram.
  it('the move registry covers each body, region subtree, end dot, and wire junction', () => {
    // a nested scene: a cut holding an atom (its dangling ports become wire-owned
    // end dots), a root ref, and a THREE-terminal wire (whose routed Steiner point
    // is a junction) — every unit taxon is present, junctions included.
    const b = new DiagramBuilder()
    const inner = b.cut(b.root)
    b.atom(inner, relSig([IOTA]))
    const r0 = b.ref(b.root, 'R', relSig([IOTA]))
    const r1 = b.ref(b.root, 'S', relSig([IOTA]))
    const r2 = b.ref(b.root, 'T', relSig([IOTA]))
    b.wire( [
      { node: r0, port: { kind: 'arg', index: 0 } },
      { node: r1, port: { kind: 'arg', index: 0 } },
      { node: r2, port: { kind: 'arg', index: 0 } },
    ], IOTA)
    const e = mkEngine(b.build(), [])
    recomputeRegions(e)

    const units = movableUnits(e)
    // the fixture must actually exercise all four taxa, or the test is vacuous
    expect(units.some((u) => u.kind === 'carrier'), 'fixture has carrier units').toBe(true)
    expect(units.some((u) => u.kind === 'region'), 'fixture has region units').toBe(true)
    expect(units.some((u) => u.kind === 'endDot'), 'fixture has wire-owned end-dot units').toBe(true)
    expect(units.some((u) => u.kind === 'junction'), 'fixture has wire junction units').toBe(true)

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
    const r = [0, 1, 2, 3, 4, 5].map((i) => b.ref(b.root, `R${i}`, relSig([IOTA, IOTA])))
    for (let i = 0; i < 6; i++) {
      b.wire( [{ node: r[i]!, port: { kind: 'arg', index: 1 } }, { node: r[(i + 1) % 6]!, port: { kind: 'arg', index: 0 } }], IOTA)
    }
    const e = mkEngine(b.build(), [])
    // a WIDE hard seed (ports facing wrong ways across long spans): the
    // faster D1 solver rested the old 4-ref spiral seed inside two publish
    // quanta, which says nothing about streaming — the fixture must genuinely
    // need several quanta for the ≥3-distinct-publishes assertion to measure
    // incrementality rather than scene difficulty.
    r.forEach((id, i) => {
      const body = e.bodies.get(id)!
      body.pos = { x: Math.cos((i / 6) * 2 * Math.PI) * 70, y: Math.sin((i / 6) * 2 * Math.PI) * 70 }
      body.theta = i * 2.4
    })
    recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
    const rawScore = layoutScore(e)

    const opt = new LayoutOptimizer(0xace4)
    opt.sync(e, null)
    // sync must NOT relax: the initial best is the raw seed itself (= the live
    // layout, no jump), so the app has something to approach from frame one.
    expect(Math.abs(opt.best()!.score - rawScore), 'sync publishes the raw seed, un-relaxed')
      .toBeLessThan(1e-6 * (rawScore + 1))

    const seq: number[] = []
    // units are greedy DOF-sweeps now (ms-scale), not 50-settle-step quanta
    for (let k = 0; k < 120; k++) { opt.tick(null, 0); seq.push(opt.best()!.score) }
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

describe('the published best-store is monotone (USER law: only the best yet found is stored)', () => {
  /** A raw, legal walk-heavy scene (four cyclically-wired refs). */
  function rawCycle(): Engine {
    const b = new DiagramBuilder()
    const r = [0, 1, 2, 3].map((i) => b.ref(b.root, `R${i}`, relSig([IOTA, IOTA])))
    for (let i = 0; i < 4; i++) {
      b.wire( [{ node: r[i]!, port: { kind: 'arg', index: 1 } }, { node: r[(i + 1) % 4]!, port: { kind: 'arg', index: 0 } }], IOTA)
    }
    const e = mkEngine(b.build(), [])
    let i = 0
    for (const [, x] of e.bodies) { x.pos = { x: Math.cos(i * 1.7) * 18, y: Math.sin(i * 1.7) * 18 }; i++ }
    recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
    return e
  }

  it('no published best ever rises across the whole run (descend + calibrate + hop)', () => {
    const opt = new LayoutOptimizer(0xace4)
    opt.sync(rawCycle(), null)
    let last = opt.best()!.score
    for (let k = 0; k < 60; k++) {
      opt.tick(null, 0)
      const s = opt.best()!.score
      expect(s, `published best rose ${last} → ${s} at unit ${k}`).toBeLessThanOrEqual(last + 1e-9)
      last = s
    }
  })

  it('adoptLive of a WORSE layout is ignored — a stale/racy adopt never raises the best', () => {
    const e = rawCycle()
    const opt = new LayoutOptimizer(0xace4)
    opt.sync(e, null)
    for (let k = 0; k < 25; k++) opt.tick(null, 0) // descend + calibrate + hop to a good best
    const before = opt.best()!.score

    // the worker's best and the client's mirrored best diverge asynchronously, so
    // adoptLive can be handed a score above the worker's true best — it must not
    // raise the monotone best-store.
    const worse = mkEngine(e.d, [])
    for (const [id, b] of worse.bodies) { const src = e.bodies.get(id)!; b.pos = { x: src.pos.x * 3, y: src.pos.y * 3 + 10 }; b.theta = src.theta + 1 }
    worse.frame = e.frame; worse.scale = e.scale
    recomputeRegions(worse)
    opt.adoptLive(worse, layoutScore(worse))

    expect(opt.best()!.score, 'adoptLive of a worse layout must not raise the best-store')
      .toBeLessThanOrEqual(before)
  })
})
