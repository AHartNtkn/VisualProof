import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { mkEngine } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, establishFrame, settleStep, wireEnergy, contentEnergy } from '../../src/view/relax'

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
  const a = db.ref(db.root, 'A', relSig([TERM]))
  const b = db.ref(db.root, 'B', relSig([TERM]))
  db.wire(db.root, [{ node: a, port: { kind: 'arg', index: 0 } }, { node: b, port: { kind: 'arg', index: 0 } }], TERM)
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
