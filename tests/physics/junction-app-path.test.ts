import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { mkEngine, carryOver, type WireView, type WireLeg, type WireLegEnd } from '../../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../../src/view/relax'
import { mkLegCache } from '../../src/view/elastica'

/**
 * APP-PATH JUNCTION RESTRUCTURING REPRODUCTIONS (all FAIL now, by design).
 *
 * The batch/pinned-stationary NNI test (junctions.test.ts) passes: with the four
 * terminals held motionless, the wire's branch DOFs reach a zero-accept sweep and the
 * topology gate flips to the optimal PAIRING. But that gate re-pairs a FIXED set of
 * branch points only. The live app exposes three further gaps the pairing move cannot
 * cover, established by observation (.superpowers/sdd/junction-app-path-diagnosis.md):
 *
 *  (a) Branch COUNT + adjacency are chosen once by buildJunctionTree on the mkEngine
 *      spiral seed and thereafter only re-paired, never re-counted. carryOver rebuilds
 *      the adjacency FRESH from the spiral on every rewrite and copies only branch
 *      positions + leg tangents index-parallel, so any NNI flip is discarded on the next
 *      rebuild (OBSERVED: flip reverts to the spiral pairing).
 *  (b) There is no SPLIT/MERGE move: a junction placed at a non-full topology can never
 *      grow into the lower-energy full Steiner tree — "new branchings don't emerge".
 *  (c) The junction skeleton (branch positions + per-leg tangent DOFs) is PERSISTENT
 *      STATE carried and locally perturbed across configurations, not an OUTPUT derived
 *      from the terminal boundary — so a warm-perturbed junction traps above the shape a
 *      memoryless rebuild finds (the inter-branch segment behaves as a stored "bar":
 *      OBSERVED bar tangent frozen at 0.068rad vs the boundary-determined 0.419rad).
 *
 * All three must PASS once the junction topology (count + adjacency + shape) is a pure
 * function of the current terminal boundary rather than carried, spiral-seeded state.
 */

const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
function nWay(k: number): Diagram {
  const b = new DiagramBuilder()
  const rs = Array.from({ length: k }, (_, i) => b.ref(b.root, `n${i}`, rel(3)))
  b.wire(b.root, rs.map((n) => ({ node: n, port: { kind: 'arg' as const, index: 0 } })))
  return b.build()
}
const refIds = (e: ReturnType<typeof mkEngine>): string[] =>
  [...e.bodies.values()].filter((x) => x.kind === 'ref').map((x) => x.id)
const theWire = (e: ReturnType<typeof mkEngine>): WireView =>
  [...e.wires.values()].find((x) => x.binds.length >= 3)!
const topoSig = (w: WireView): string =>
  w.legs.map((l) => `${l.a.kind[0]}${l.a.i}-${l.b.kind[0]}${l.b.i}`).sort().join(',')

/** Place terminals at a layout, re-fit the frame, and settle through the APP pathway:
    one `settleStep(e, pinned)` per frame to a fixed point (mechanically identical to the
    app's per-rAF loop — the terminals are the drag-pinned set). */
function driveTo(e: ReturnType<typeof mkEngine>, layout: readonly { x: number; y: number }[]): number {
  const ids = refIds(e)
  ids.forEach((id, n) => { const b = e.bodies.get(id)!; b.pos = { ...layout[n]! }; b.theta = 0 })
  e.frame = null
  const pinned = new Set(ids)
  for (let t = 0; t < 4000; t++) if (!settleStep(e, pinned)) break
  return totalEnergy(e)
}

function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: readonly { x: number; y: number }[]): void {
  const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n }); const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const B0 = { x: (c[i]!.x + c[j]!.x) / 2, y: (c[i]!.y + c[j]!.y) / 2 }, B1 = { x: (c[k]!.x + c[l]!.x) / 2, y: (c[k]!.y + c[l]!.y) / 2 }
  const chord = (f: { x: number; y: number }, t: { x: number; y: number }): number => Math.atan2(t.y - f.y, t.x - f.x)
  const mk = (a: WireLegEnd, b: WireLegEnd, f: { x: number; y: number }, t: { x: number; y: number }): WireLeg => ({ a, b, angA: chord(f, t), angB: chord(f, t), cache: mkLegCache() })
  w.branches.length = 0; w.branches.push(B0, B1); w.legs.length = 0
  for (const lg of [mk(bind(i), br(0), c[i]!, B0), mk(bind(j), br(0), c[j]!, B0), mk(bind(k), br(1), c[k]!, B1), mk(bind(l), br(1), c[l]!, B1), mk(br(0), br(1), B0, B1)]) w.legs.push(lg)
}
/** A single degree-4 star: ONE branch, four terminal legs, no internal edge. There is
    no SPLIT move, so this can never grow into the lower-energy two-branch Steiner tree. */
function setStar(w: WireView, c: readonly { x: number; y: number }[]): void {
  const B0 = { x: c.reduce((s, p) => s + p.x, 0) / c.length, y: c.reduce((s, p) => s + p.y, 0) / c.length }
  const chord = (f: { x: number; y: number }, t: { x: number; y: number }): number => Math.atan2(t.y - f.y, t.x - f.x)
  w.branches.length = 0; w.branches.push(B0); w.legs.length = 0
  for (let n = 0; n < c.length; n++) w.legs.push({ a: { kind: 'bind', i: n }, b: { kind: 'branch', i: 0 }, angA: chord(c[n]!, B0), angB: chord(c[n]!, B0), cache: mkLegCache() })
}

const RECT = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]
const FLOAT_NOISE = 1.0

describe('junction restructuring under the app per-frame pathway', () => {
  it('(a) an NNI flip survives a rewrite rebuild (carryOver must preserve topology)', () => {
    // Reach the flipped optimal pairing on the pinned wide rect (the passing NNI case).
    const e = mkEngine(nWay(4), [])
    driveTo(e, RECT)
    const flipped = topoSig(theWire(e))
    // Simulate the app's rewrite rebuild: new engine (same diagram) + carryOver + seedProject.
    const next = mkEngine(nWay(4), [])
    carryOver(e, next)
    seedProject(next)
    const rebuilt = topoSig(theWire(next))
    // carryOver rebuilds adjacency from the fresh spiral seed and copies only branch
    // positions + tangents, so the flip is discarded and the topology reverts to spiral.
    expect(rebuilt, `flipped topology '${flipped}' was not preserved across a rebuild — carryOver reverted it to '${rebuilt}'`)
      .toBe(flipped)
  })

  it('(b) a degree-4 star reaches the two-branch Steiner energy (a split must emerge)', () => {
    // Hand-place a single degree-4 star on the wide rect and settle the app way.
    const star = mkEngine(nWay(4), [])
    const sIds = refIds(star)
    sIds.forEach((id, n) => { const b = star.bodies.get(id)!; b.pos = { ...RECT[n]! }; b.theta = 0 })
    star.frame = null
    setStar(theWire(star), RECT)
    const eStar = driveTo(star, RECT)
    // The two-branch full Steiner tree on the SAME geometry — the reachable lower energy.
    const opt = mkEngine(nWay(4), [])
    const oIds = refIds(opt)
    oIds.forEach((id, n) => { const b = opt.bodies.get(id)!; b.pos = { ...RECT[n]! }; b.theta = 0 })
    opt.frame = null
    setPairing(theWire(opt), 0, 1, 2, 3, RECT)
    const eOpt = driveTo(opt, RECT)
    expect(theWire(star).branches.length, 'the star never split — branch count is frozen at construction').toBe(2)
    expect(eStar, `degree-4 star settled to E=${eStar.toFixed(1)}, two-branch tree E=${eOpt.toFixed(1)} — no split move exists`)
      .toBeLessThanOrEqual(eOpt + FLOAT_NOISE)
  })

  it('(c) perturb-and-resettle matches a memoryless fresh rebuild (derived-shape law)', () => {
    // WARM: settle at RECT, then swing the right pair far up and re-settle, carrying the
    // stored junction skeleton (branch positions + tangent DOFs).
    const P1 = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: 40 }, { x: 40, y: 64 }]
    const warm = mkEngine(nWay(4), [])
    driveTo(warm, RECT)
    const eWarm = driveTo(warm, P1)
    // MEMORYLESS: a fresh engine built straight to P1 — the shape the boundary determines.
    const eFresh = driveTo(mkEngine(nWay(4), []), P1)
    expect(eWarm, `warm-perturbed E=${eWarm.toFixed(1)} exceeds memoryless rebuild E=${eFresh.toFixed(1)} — the stored skeleton traps the wire above its boundary-determined shape`)
      .toBeLessThanOrEqual(eFresh + FLOAT_NOISE)
  })
})
