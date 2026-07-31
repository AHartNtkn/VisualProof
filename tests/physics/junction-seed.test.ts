import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { carryOver, mkEngine, wireRouteSpaces, wireTerminalPoints } from '../../src/view/engine'
import { recomputeRegions, seedProject } from '../../src/view/relax'
import { solveTarget } from '../../src/view/route/network'
import type { WireNet } from '../../src/view/route/network'
import { UNARY } from '../fixtures/zero-signature'

/**
 * JUNCTION SPAWN POSITIONS ARE SOLVED, NOT STALE SEEDS (USER 2026-07-30: a
 * fresh wire's junction spawned "usually close to the center point of the
 * diagram" and spent the whole opening walking to its optimum — in the same
 * time it could simply spawn AT the optimum).
 *
 * Mechanism: mkEngine stars a ≥3-terminal wire's junction at the terminal
 * centroid of the SEED layout; carryOver then moves the bodies to the carried
 * layout, leaving a NEW wire's junction at the stale seed. The law: after the
 * spawn pipeline (carryOver + seedProject), a wire whose junction state was
 * not carried sits at the fixed-topology target solved from its CURRENT
 * terminals. Carried junction state is untouched (re-deriving it would be
 * argmin-tracking of state that must glide).
 */

/** Three unary refs; `withWire` adds the 3-terminal wire joining them. */
function threeRefs(withWire: boolean): { d: Diagram; refs: string[]; wid: string | null } {
  const b = new DiagramBuilder()
  const refs = ['A', 'B', 'C'].map((n) => b.ref(b.root, n, UNARY))
  const wid = withWire
    ? b.wire(b.root, refs.map((node) => ({ node, port: { kind: 'arg' as const, index: 0 } })))
    : null
  return { d: b.build(), refs, wid }
}

/** The fixed-topology junction target solved from the engine's live geometry. */
function solvedJunctions(e: ReturnType<typeof mkEngine>, wid: string): WireNet['junctions'] {
  const w = e.wires.get(wid)!
  const clone: WireNet = { junctions: w.net.junctions.map((p) => ({ ...p })), edges: [...w.net.edges] }
  solveTarget(clone, wireTerminalPoints(e, w), wireRouteSpaces(e).space(wid), 60)
  return clone.junctions
}

describe('fresh wire junctions spawn at their solved optimum', () => {
  it('a wire spawned at a rewrite seeds its junction from the carried terminals, not the stale seed', () => {
    const prev0 = threeRefs(false)
    const prev = mkEngine(prev0.d, [])
    seedProject(prev)
    // the carried layout: the three refs clustered far from the origin
    const at = [{ x: 60, y: 40 }, { x: 82, y: 40 }, { x: 71, y: 62 }]
    prev0.refs.forEach((id, k) => { prev.bodies.get(id)!.pos = at[k]! })
    recomputeRegions(prev)

    const next0 = threeRefs(true)
    const next = mkEngine(next0.d, [])
    const carried = carryOver(prev, next)
    seedProject(next, false, carried)

    const wid = next0.wid!
    const junctions = next.wires.get(wid)!.net.junctions
    expect(junctions.length, 'sanity: the 3-terminal wire stars one junction').toBe(1)
    const target = solvedJunctions(next, wid)[0]!
    const off = Math.hypot(junctions[0]!.x - target.x, junctions[0]!.y - target.y)
    expect(
      off,
      `the fresh junction sits ${off.toFixed(1)} wu from its solved target — it spawned at the stale seed`,
    ).toBeLessThan(0.01)
  })

  it('carried junction state is NOT re-derived by the spawn pipeline', () => {
    const both = threeRefs(true)
    const prev = mkEngine(both.d, [])
    seedProject(prev)
    // glide state: the carried junction rests displaced from the solved target
    const pw = prev.wires.get(both.wid!)!
    const displaced = { x: pw.net.junctions[0]!.x + 14, y: pw.net.junctions[0]!.y + 9 }
    pw.net.junctions[0] = displaced

    const next = mkEngine(threeRefs(true).d, [])
    const carried = carryOver(prev, next)
    seedProject(next, false, carried)

    const junction = next.wires.get(both.wid!)!.net.junctions[0]!
    const target = solvedJunctions(next, both.wid!)[0]!
    expect(
      Math.hypot(junction.x - target.x, junction.y - target.y),
      'the carried (displaced) junction must keep its glide state, not snap to the solved target',
    ).toBeGreaterThan(1)
  })
})
