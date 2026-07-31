import { describe, expect, it } from 'vitest'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import {
  attachLayoutSearch, recomputeRegions, resolveOverlaps, settle, settleStep, PRESENT_SLOW, WIREP,
} from '../../src/view/relax'
import type { LayoutSearch } from '../../src/view/relax'
import { applyLayoutSnapshot, layoutScore, layoutSnapshot } from '../../src/view/optimize'
import type { LayoutBest } from '../../src/view/optimize'
import { CONTRACT_TOL, SPLIT_EPS } from '../../src/view/route/network'
import type { Vec2 } from '../../src/view/vec'
import { identityJunctionScene } from '../fixtures/zero-signature'

/**
 * PRESENTATION CONTINUITY OF WIRE STATE (USER: wires "snap to the new position
 * quickly, or sometimes lag at old positions and snap to catch up").
 *
 * The uniform-locality law governs the VISIBLE layout: every visible DOF takes
 * bounded per-frame steps at ONE presentation pace. Bodies obey it (approach
 * bound = travelCap/PRESENT_SLOW · scale). Wire junctions are visible DOFs of
 * the same layout, so the SAME bound governs them.
 *
 * State-level, drawing-independent: the drawn stroke is derived from bodies +
 * junctions, and topology events are state-continuous by construction (a
 * contraction fires only within CONTRACT_TOL coincidence; a split opens by
 * SPLIT_EPS), so bounded junction steps make the per-frame drawing change
 * small — continuity as a consequence, never a mechanism.
 *
 * Measured defects (presentation path, 2026-07-30) each case pins down:
 *  1. approachStep adopts a best's nets WHOLE — junction state teleports to
 *     the searcher's settled optimum in one frame (~10 wu on zeroIsNat@17).
 *  2. the presentation walk runs substeps·travelCap = 2.2 wu of junction
 *     travel per frame — 20× the body presentation bound.
 */

const presentationBound = (e: Engine): number => (WIREP.travelCap / PRESENT_SLOW) * e.scale

type JState = Map<string, { edges: string; pts: Vec2[] }>
const junctionsOf = (e: Engine): JState => {
  const out: JState = new Map()
  for (const [wid, w] of e.wires) {
    out.set(wid, {
      edges: JSON.stringify(w.net.edges),
      pts: w.net.junctions.map((p) => ({ ...p })),
    })
  }
  return out
}

/** Symmetric Hausdorff distance between two point sets (0 when both empty). */
function hausdorff(a: readonly Vec2[], b: readonly Vec2[]): number {
  if (a.length === 0 && b.length === 0) return 0
  if (a.length === 0 || b.length === 0) return Infinity
  const dir = (P: readonly Vec2[], Q: readonly Vec2[]): number => {
    let m = 0
    for (const p of P) {
      let best = Infinity
      for (const q of Q) best = Math.min(best, Math.hypot(p.x - q.x, p.y - q.y))
      m = Math.max(m, best)
    }
    return m
  }
  return Math.max(dir(a, b), dir(b, a))
}

/** Run `frames` searched frames; return the worst same-topology junction step,
    the worst topology-event state displacement, and the total junction travel. */
function measure(e: Engine, frames: number): { worstStep: number; worstTopo: number; travel: number } {
  let prev = junctionsOf(e)
  let worstStep = 0, worstTopo = 0, travel = 0
  for (let i = 0; i < frames; i++) {
    settleStep(e)
    const cur = junctionsOf(e)
    for (const [wid, now] of cur) {
      const was = prev.get(wid)
      if (was === undefined) continue
      if (was.edges === now.edges) {
        for (let j = 0; j < now.pts.length; j++) {
          const d = Math.hypot(now.pts[j]!.x - was.pts[j]!.x, now.pts[j]!.y - was.pts[j]!.y)
          worstStep = Math.max(worstStep, d)
          travel += d
        }
      } else {
        const d = hausdorff(was.pts, now.pts)
        worstTopo = Math.max(worstTopo, d)
        travel += d
      }
    }
    prev = cur
  }
  return { worstStep, worstTopo, travel }
}

describe('wire junctions move at the presentation pace (no teleports, no 20× walk)', () => {
  it('adopting a searched best never teleports junction state', () => {
    const e = mkEngine(identityJunctionScene(), [])
    recomputeRegions(e)
    resolveOverlaps(e)
    settleStep(e) // establishes the frame (pre-presentation solver tick)

    // The searched BEST: relax a scratch copy of this very layout — exactly
    // what the worker's phase-0 descent publishes — and hand the frame loop
    // that fixed snapshot. (Its wire topology differs from the live seed's.)
    const scratch = mkEngine(identityJunctionScene(), [])
    scratch.frame = e.frame
    scratch.scale = e.scale
    scratch.slotShift = e.slotShift
    applyLayoutSnapshot(scratch, layoutSnapshot(e, 0))
    recomputeRegions(scratch)
    settle(scratch, 400)
    const best: LayoutBest = layoutSnapshot(scratch, layoutScore(scratch))

    const search: LayoutSearch = {
      sync: () => {},
      best: () => best,
      adoptLive: () => {},
      searching: true,
    }
    attachLayoutSearch(e, search)

    const bound = presentationBound(e)
    // a topology event may displace junction identity by its own construction
    // scales: contraction merges within CONTRACT_TOL, a split opens by SPLIT_EPS
    const topoTol = bound + SPLIT_EPS + CONTRACT_TOL + 1e-9
    const { worstStep, worstTopo, travel } = measure(e, 400)

    expect(travel, 'sanity: the scenario exercises junction motion at all').toBeGreaterThan(0)
    // topoTol (not the bare bound): a contract+split round trip inside one
    // frame restores the edge list, so same-edges frames may contain two
    // coincidence-scale topology events — see the walk-pace case below.
    expect(
      worstStep,
      `a junction moved ${worstStep.toFixed(2)} wu in one frame; the presentation bound is ${bound.toFixed(3)} wu (+ coincidence scales)`,
    ).toBeLessThanOrEqual(topoTol)
    expect(
      worstTopo,
      `a topology change displaced junction state by ${worstTopo.toFixed(2)} wu; topology events are coincidence-scale (${topoTol.toFixed(3)} wu)`,
    ).toBeLessThanOrEqual(topoTol)
  })

  it('the presentation walk itself moves junctions at the presentation pace', () => {
    const e = mkEngine(identityJunctionScene(), [])
    recomputeRegions(e)
    resolveOverlaps(e)
    settle(e, 400) // full local rest — the walk has nothing left to do

    // no best available: searched frames run the presentation WALK alone
    const search: LayoutSearch = {
      sync: () => {},
      best: () => null,
      adoptLive: () => {},
      searching: true,
    }
    attachLayoutSearch(e, search)

    // displace one junction well off its rest; the walk must bring it back —
    // at the presentation pace, never at solver amplitude
    const w0 = [...e.wires.values()].find((w) => w.net.junctions.length > 0)
    expect(w0, 'sanity: the scene has a junction-bearing wire').toBeDefined()
    const j0 = w0!.net.junctions[0]!
    w0!.net.junctions[0] = { x: j0.x + 8, y: j0.y + 8 }

    const bound = presentationBound(e)
    const topoTol = bound + SPLIT_EPS + CONTRACT_TOL + 1e-9
    const { worstStep, worstTopo, travel } = measure(e, 300)

    expect(travel, 'sanity: the walk moves the displaced junction back').toBeGreaterThan(1)
    // topoTol on BOTH branches: a contract+split ROUND TRIP inside one frame
    // restores the edge list byte-identically, so a same-edges frame can still
    // contain two coincidence-scale topology events (observed: walk step +
    // CONTRACT_TOL/2 merge + SPLIT_EPS/2 reopen ≈ bound + 0.005).
    expect(
      worstStep,
      `the walk moved a junction ${worstStep.toFixed(2)} wu in one frame; the presentation bound is ${bound.toFixed(3)} wu (+ coincidence scales)`,
    ).toBeLessThanOrEqual(topoTol)
    expect(
      worstTopo,
      `a topology change displaced junction state by ${worstTopo.toFixed(2)} wu; topology events are coincidence-scale (${topoTol.toFixed(3)} wu)`,
    ).toBeLessThanOrEqual(topoTol)
  })
})
