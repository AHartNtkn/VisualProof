import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { mkEngine, carryOver, type WireView, type WireLeg, type WireLegEnd } from '../../src/view/engine'
import { settleStep, seedProject, totalEnergy } from '../../src/view/relax'
import { mkLegCache } from '../../src/view/elastica'

/**
 * REBUILD CARRY — junction topology T is CARRIED state (Task 1: state = (T, b, τ)).
 *
 * A wire's junction state is the triple (T, b, τ): the tree TOPOLOGY T (which
 * terminals/branch vertices each edge connects — the leg end-structure), the branch
 * POSITIONS b (`WireView.branches`), and the per-half-edge TANGENTS τ (per-leg
 * `angA/angB`). Diagnosed cause (a): the app rebuilds the engine on every diagram
 * change (`mkEngine` + `carryOver` + `seedProject`) and the old `carryOver` inherited
 * the NEW engine's FRESH soap-tree adjacency — re-deriving T from the spiral seed and
 * discarding any achieved restructuring. Under the accepted design T is a genuine
 * coordinate (stored, like node positions): nothing ever re-derives it from geometry,
 * so `carryOver` must copy the surviving wire's T verbatim, keyed on wire identity —
 * never on branch count, never from the seed.
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
/** A lossy-but-deterministic topology fingerprint: each leg as its two end
    (kind-initial, index) pairs, sorted. Adjacency only — position/tangent free. */
const endTag = (end: WireLegEnd): string => `${end.kind[0]}${'i' in end ? end.i : ''}`
const topoSig = (w: WireView): string =>
  w.legs.map((l) => `${endTag(l.a)}-${endTag(l.b)}`).sort().join(',')

/** Impose the two-branch Steiner tree pairing {i,j}|{k,l} on a 4-terminal wire — a
    concrete topology to carry, independent of what the soap-tree seed produced. */
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: readonly { x: number; y: number }[]): void {
  const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n })
  const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const B0 = { x: (c[i]!.x + c[j]!.x) / 2, y: (c[i]!.y + c[j]!.y) / 2 }
  const B1 = { x: (c[k]!.x + c[l]!.x) / 2, y: (c[k]!.y + c[l]!.y) / 2 }
  const chord = (f: { x: number; y: number }, t: { x: number; y: number }): number => Math.atan2(t.y - f.y, t.x - f.x)
  const mk = (a: WireLegEnd, b: WireLegEnd, f: { x: number; y: number }, t: { x: number; y: number }): WireLeg =>
    ({ a, b, angA: chord(f, t), angB: chord(f, t), cache: mkLegCache() })
  w.branches.length = 0; w.branches.push(B0, B1); w.legs.length = 0
  for (const lg of [mk(bind(i), br(0), c[i]!, B0), mk(bind(j), br(0), c[j]!, B0), mk(bind(k), br(1), c[k]!, B1), mk(bind(l), br(1), c[l]!, B1), mk(br(0), br(1), B0, B1)]) w.legs.push(lg)
}

const RECT = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]

/** Place terminals at a layout, re-fit the frame, and settle through the APP pathway:
    one `settleStep(e, pinned)` per frame to a fixed point (the terminals are the
    drag-pinned set — mechanically the app's per-rAF loop). */
function driveTo(e: ReturnType<typeof mkEngine>, layout: readonly { x: number; y: number }[]): number {
  const ids = refIds(e)
  ids.forEach((id, n) => { const b = e.bodies.get(id)!; b.pos = { ...layout[n]! }; b.theta = 0 })
  e.frame = null
  const pinned = new Set(ids)
  for (let t = 0; t < 4000; t++) if (!settleStep(e, pinned)) break
  return totalEnergy(e)
}

describe('junction state (T, b, τ) is carried across a rewrite rebuild', () => {
  it('carryOver preserves an imposed topology T verbatim (never re-derived from the fresh seed)', () => {
    // The fresh soap-tree seed's topology for the wide rect.
    const seedEngine = mkEngine(nWay(4), [])
    const seedSig = topoSig(theWire(seedEngine))

    // Impose a concrete two-branch pairing that DIFFERS from the seed (guard against a
    // vacuous test: if the seed already draws this pairing, choose the other one).
    const e = mkEngine(nWay(4), [])
    const pairings: [number, number, number, number][] = [[0, 1, 2, 3], [0, 2, 1, 3], [0, 3, 1, 2]]
    let imposedSig = ''
    for (const [i, j, k, l] of pairings) {
      setPairing(theWire(e), i, j, k, l, RECT)
      imposedSig = topoSig(theWire(e))
      if (imposedSig !== seedSig) break
    }
    expect(imposedSig, 'no pairing differs from the seed — test would be vacuous').not.toBe(seedSig)

    // The app's rewrite rebuild: a FRESH engine for the same diagram + carryOver + seedProject.
    const next = mkEngine(nWay(4), [])
    carryOver(e, next)
    seedProject(next)

    expect(topoSig(theWire(next)), 'carryOver re-derived T from the fresh spiral seed instead of carrying the surviving wire\'s topology')
      .toBe(imposedSig)
    expect(topoSig(theWire(next)), 'the carried topology collapsed back onto the seed').not.toBe(seedSig)
  })

  it('an NNI flip survives a rewrite rebuild (revised repro (a): carryOver carries T)', () => {
    // Reach the flipped optimal pairing on the pinned wide rect (the passing NNI case).
    const e = mkEngine(nWay(4), [])
    driveTo(e, RECT)
    const flipped = topoSig(theWire(e))

    // Simulate the app's rewrite rebuild: new engine (same diagram) + carryOver + seedProject.
    const next = mkEngine(nWay(4), [])
    carryOver(e, next)
    seedProject(next)

    expect(topoSig(theWire(next)), `flipped topology '${flipped}' was not preserved across a rebuild — carryOver reverted it`)
      .toBe(flipped)
  })
})
