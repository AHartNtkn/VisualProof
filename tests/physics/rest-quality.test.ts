import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, establishFrame, settleStep, wireEnergy, contentEnergy } from '../../src/view/relax'
import { LayoutOptimizer, applyLayoutSnapshot } from '../../src/view/optimize'
import { junctionCuspScene } from '../fixtures/zero-signature'

/**
 * REST QUALITY (plan Task 9, USER: "whatever it stops at shouldn't be obviously
 * wrong"). Local descent used to certify rests that are obviously wrong — a node
 * whose one wire loops absurdly when a rotation would relax it — because the
 * corridor was chosen by the polyline SOFT metric, not the drawn-curve energy it
 * is charged. At a Dijkstra crossing the route gains a waypoint and the Hobby
 * chain reshapes: the drawn-curve energy JUMPS while the soft cost barely moves,
 * carving milliradian micro-wells the strict-gated descent rests inside.
 *
 * Contract: at a settled rest (positions pinned, rotations free), NO macroscopic
 * single-coordinate move may lower the exact energy. Here: sweeping one ref's
 * rotation over ±1.5 rad must find nothing meaningfully below the rest energy.
 */

/** Two refs wired arg-to-arg, pinned apart on the x-axis, A's rotation seeded into
    the micro-well band. The wire routes around A's disc; as A rotates, the route
    gains/loses a waypoint and the drawn-curve energy jumps — the descent rests in a
    well ~68° off-facing while a −1.5 rad rotation (toward facing) lowers E by ~40.
    Positions are pinned so only the rotations descend. */
function facingAwayPair(): { e: ReturnType<typeof mkEngine>; a: string; b: string } {
  const db = new DiagramBuilder()
  const a = db.ref(db.root, 'A', relSig([IOTA]))
  const b = db.ref(db.root, 'B', relSig([IOTA]))
  db.wire([{ node: a, port: { kind: 'arg', index: 0 } }, { node: b, port: { kind: 'arg', index: 0 } }], IOTA)
  const e = mkEngine(db.build(), [])
  e.bodies.get(a)!.pos = { x: -12, y: 0 }
  e.bodies.get(b)!.pos = { x: 12, y: 0 }
  e.bodies.get(a)!.theta = 1.4
  e.bodies.get(b)!.theta = 4.8
  recomputeRegions(e); resolveOverlaps(e); establishFrame(e); recomputeRegions(e)
  return { e, a, b }
}

const exactE = (e: ReturnType<typeof mkEngine>): number => { recomputeRegions(e); return wireEnergy(e) + contentEnergy(e) }

describe('rest quality — no obviously-wrong local rest (plan Task 9)', () => {
  it('a settled facing-away pair has no macroscopic rotation improvement at rest', () => {
    const { e, a, b } = facingAwayPair()
    const pinned = new Set([a, b]) // pin positions; rotations remain free
    for (let k = 0; k < 4000; k++) if (!settleStep(e, pinned)) break

    const Erest = exactE(e)
    const A = e.bodies.get(a)!
    const theta0 = A.theta
    let best = Erest, bestD = 0
    for (let d = -1.5; d <= 1.5 + 1e-9; d += 0.15) {
      A.theta = theta0 + d
      const E = exactE(e)
      if (E < best) { best = E; bestD = d }
    }
    A.theta = theta0
    expect(best, `rest E ${Erest.toFixed(2)}; a Δθ=${bestD.toFixed(2)} rot reaches ${best.toFixed(2)} (improvement ${(Erest - best).toFixed(2)}) — the descent rested in a micro-well`)
      .toBeGreaterThanOrEqual(Erest - 1e-3 * Math.abs(Erest))
  })
})

/**
 * JUNCTION LAW (plan Task 10, USER: "the wires themselves still aren't doing
 * local descent" — a wire resting in a cusp). A wire junction is a POSITIONAL
 * DOF, and a cusp is a barrier-separated basin: the local walk settles the
 * junction only toward the Weiszfeld length-target (gated on the true energy),
 * so when the better basin lies across an obstacle barrier the walk cannot reach
 * it — and aggressive full-energy junction descent in the walk was MEASURED to
 * defeat basin hopping (junctions are positional; the Task-9 locality result
 * applies). So crossing a junction cusp is the SEARCH layer's job — the
 * `displaceJunction` hop, the junction analog of `displaceSubtree`. This law is
 * therefore asserted on the ANNEALER'S BEST, not the local walk's rest.
 *
 * Junctions are wire waypoints and content (node spacing, scope rings) is
 * junction-invariant, so a junction defect's scale is the WIRE energy (content —
 * here 98.7% of the total — would dilute the law into noise).
 */
function junctionSweep(e: ReturnType<typeof mkEngine>): { restWire: number; best: number; detail: string } {
  recomputeRegions(e)
  const restWire = wireEnergy(e)
  const restTotal = restWire + contentEnergy(e)
  let best = restTotal, detail = 'no junction beats rest'
  for (const [wid, w] of e.wires) {
    for (let j = 0; j < w.net.junctions.length; j++) {
      const save = { ...w.net.junctions[j]! }
      for (let dir = 0; dir < 16; dir++) {
        const ang = (dir / 16) * 2 * Math.PI
        for (const r of [2, 5, 10, 20]) {
          w.net.junctions[j] = { x: save.x + Math.cos(ang) * r, y: save.y + Math.sin(ang) * r }
          recomputeRegions(e)
          const E = wireEnergy(e) + contentEnergy(e)
          if (E < best) { best = E; detail = `${wid} j${j} ${(ang * 180 / Math.PI).toFixed(0)}deg r${r}` }
        }
      }
      w.net.junctions[j] = save
    }
  }
  recomputeRegions(e)
  return { restWire, best: restTotal - best, detail } // best := improvement (≥0)
}

describe('rest quality — the search crosses the junction cusp (plan Task 10)', () => {
  it("the annealer's best on the junction cusp scene admits no macroscopic junction improvement", () => {
    const e = mkEngine(junctionCuspScene(), [])
    recomputeRegions(e); resolveOverlaps(e); recomputeRegions(e)
    for (let k = 0; k < 200; k++) if (!settleStep(e)) break

    // the CUSPY local rest: the walk settles the junction into a barrier-blocked
    // basin. Its wire energy and the barrier gap (the sweep improvement it still
    // admits) are the defect the search must cross.
    const cuspWire = (recomputeRegions(e), wireEnergy(e))
    const { best: barrierGap } = junctionSweep(e)

    // pin every node so ONLY displaceJunction is applicable — isolates the
    // junction fix from whole-layout reshaping. The chain is seeded, so WHICH
    // unit crosses the barrier is a pure function of the scene; the wall clock
    // only bounds how long we wait for it (USER ruling 2026-07-24: reach the
    // target within the budget or FAIL). A fixed unit count is NOT a valid
    // budget: it couples the test to the phase schedule (streamed descent +
    // 16 calibration probes come first), which is implementation, not the
    // behavior — measured 2026-08-13, at unit 30 the chain was still
    // calibrating (T = 0) and the hop phase it exists to test had not begun.
    // Nodes are pinned and content is junction-invariant, so a published
    // score improvement IS a wire-energy improvement — drive on the score.
    // fixture sanity: the local rest must actually sit in a cusp — a zero gap
    // means the fixture no longer manufactures the defect and the test is vacuous
    expect(barrierGap, 'fixture manufactures a junction cusp').toBeGreaterThan(0)

    const pinned = new Set([...e.bodies.keys()])
    const opt = new LayoutOptimizer(0xbeef)
    opt.sync(e, pinned)
    const target = opt.best()!.score - barrierGap

    // The behavioral target is BOTH halves of the law: the published best has
    // crossed the measured barrier gap AND its own residual sweep finds no
    // improvement as large as that gap — i.e. the best does not itself sit in
    // a cusp of the scale the search just proved it can cross. Both sides of
    // every comparison are measured in-test, so the contract self-calibrates
    // to the current energy (USER ruling: no measured-constant pins). The
    // sweep is evaluated lazily, only when a new best at/below the score
    // target is published.
    const t0 = performance.now()
    let bestWire = Infinity
    let residual = Infinity
    let detail = ''
    let lastScore = Infinity
    for (;;) {
      const best = opt.best()!
      if (best.score !== lastScore) {
        lastScore = best.score
        if (best.score <= target) {
          const probe = mkEngine(junctionCuspScene(), [])
          applyLayoutSnapshot(probe, best)
          bestWire = (recomputeRegions(probe), wireEnergy(probe))
          const s = junctionSweep(probe)
          residual = s.best
          detail = s.detail
          if (residual < barrierGap) break
        }
      }
      if (performance.now() - t0 >= 20_000) break
      opt.tick(null, 0)
    }

    // (1) BEHAVIORAL — the search crossed the barrier: the best is below the cuspy
    // local rest by at least the measured barrier gap. Pins THE defect directly,
    // independent of any ratio class.
    expect(cuspWire - bestWire, `search must cross the cusp: cusp wireE ${cuspWire.toFixed(1)}, best ${bestWire.toFixed(1)}, barrier gap ${barrierGap.toFixed(2)}`)
      .toBeGreaterThanOrEqual(barrierGap)

    // (2) RESIDUAL — the best admits no junction improvement at the cusp scale:
    // anything the sweep still finds is smaller than the barrier the search
    // demonstrably crosses, leaving only the sub-gap relaxation residual (the
    // walk settles junctions to the length-constrained rest, not the
    // full-energy min, by the anneal-preservation ruling).
    expect(residual, `best junction residual ${residual.toFixed(2)} at ${detail} is not below the measured barrier gap ${barrierGap.toFixed(2)}`)
      .toBeLessThan(barrierGap)
  })
})
