import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg, traceLeg, type WireView, type WireLeg, type WireLegEnd } from '../../src/view/engine'
import { settle, settleStep, totalEnergy } from '../../src/view/relax'
import { QN, mkLegCache } from '../../src/view/elastica'

/**
 * JUNCTION EQUILIBRATION + RESTRUCTURING REPRODUCTIONS (both FAIL now, by design).
 *
 * These reproduce two user-reported defects in the FROZEN energy-minimization
 * junction paradigm. Both are known-failing: the repo carries no active `it.fails`
 * convention (the only mentions in relax.test.ts are historical comments noting the
 * old `it.fails` were REMOVED once the drift they marked was fixed), so these are
 * committed plainly failing. They must PASS once the junction energy model is
 * corrected to (a) equilibrate a symmetric triple junction to the soap-film 120°
 * and (b) permit discrete branch-tree restructuring toward the lower-energy topology.
 *
 * MECHANICAL ROOT (diagnosed, see .superpowers/sdd/junction-diagnosis.md):
 *  - Branch-leg tangents AT a branch point are hard-slaved to the trunk-tributary
 *    `trunkTarget(chordDir, branchPhi)` rule (engine.ts resolveLeg, th0 @ leg.a.kind
 *    === 'branch' and th1 @ leg.b.kind === 'branch'), with a stiff WELL_S=25 arrival
 *    well. The branch POSITION + branchPhi DOFs descend leg tension/bend UNDER those
 *    clamped tangents, so the settled minimum is a straight-trunk-plus-tangential-
 *    merge geometry, never the Plateau 120° star. (Measured: the branch point sits at
 *    a STRICT energy minimum — a 13x13 grid probe finds no lower neighbour — yet the
 *    meeting angles are ~99/99/161, so this is an ENERGY-MODEL defect, not a descent
 *    failure.)
 *  - The junction TOPOLOGY (which terminals pair through which branch) is chosen ONCE
 *    by buildJunctionTree on the mkEngine spiral seed and then FROZEN: descentDofs
 *    exposes only continuous branch-position/angle DOFs, and the sole post-construction
 *    branch rewrite (reseedUnrepresentableBranches) copies branch POSITIONS only, never
 *    leg adjacency. No mover can swap partners, so a suboptimal seed topology is permanent.
 */

const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
const between = (a: number, b: number): number => { let x = Math.abs((a - b) * 180 / Math.PI) % 360; if (x > 180) x = 360 - x; return x }

/** Three symmetric unary refs sharing one 3-way line of identity. Symmetric by
    construction (identical nodes, identical ports), so a soap-film energy model
    must rest with all three meeting angles equal — i.e. exactly 120°. */
function symTriple(): { d: Diagram; b: WireId[] } {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'p', rel(1))
  const r2 = b.ref(b.root, 'q', rel(1))
  const r3 = b.ref(b.root, 'r', rel(1))
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
    { node: r3, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [] }
}

/** Four refs sharing one 4-way line: a Steiner tree of two branch points. */
function fourWay(): { d: Diagram; b: WireId[] } {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'a', rel(3))
  const r2 = b.ref(b.root, 'bb', rel(3))
  const r3 = b.ref(b.root, 'cc', rel(3))
  const r4 = b.ref(b.root, 'dd', rel(3))
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
    { node: r3, port: { kind: 'arg', index: 0 } },
    { node: r4, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [] }
}

/** Force a 4-terminal wire into pairing (i,j)|(k,l): two branch points B0,B1 with
    edges i->B0, j->B0, k->B1, l->B1, B0->B1 (terminals are binds 0..3). Seeds each
    branch at the midpoint of its pair. This is the hand-built alternative topology
    the frozen system can never reach on its own. */
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: readonly { x: number; y: number }[]): void {
  const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n })
  const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const mk = (a: WireLegEnd, b: WireLegEnd): WireLeg => ({ a, b, hubAngle: 0, cache: mkLegCache() })
  w.legs.length = 0
  for (const lg of [mk(bind(i), br(0)), mk(bind(j), br(0)), mk(bind(k), br(1)), mk(bind(l), br(1)), mk(br(0), br(1))]) w.legs.push(lg)
  w.branches.length = 0; w.branches.push({ x: (c[i]!.x + c[j]!.x) / 2, y: (c[i]!.y + c[j]!.y) / 2 }, { x: (c[k]!.x + c[l]!.x) / 2, y: (c[k]!.y + c[l]!.y) / 2 })
  w.branchPhi.length = 0; w.branchPhi.push(0, 0)
}

/** Settle a fixed-point layout with a hard tick cap (the repo settle idiom). */
const settled4way = (): ReturnType<typeof mkEngine> => {
  const { d, b } = fourWay()
  const e = mkEngine(d, b)
  settle(e, 8000)
  return e
}

describe('junction equilibration — a symmetric triple junction must meet at 120° (soap-film Plateau)', () => {
  it('all three pairwise leg meeting angles are within tolerance of 2π/3', () => {
    const { d, b } = symTriple()
    const e = mkEngine(d, b)
    settle(e, 8000) // fixed-point settle, hard cap (repo idiom; converges in <300 ticks)
    const w = [...e.wires.values()].find((x) => x.branches.length > 0)!
    expect(w.branches, 'the symmetric triple is a one-branch Steiner tree').toHaveLength(1)

    // outgoing tangent direction of each branch leg AT the branch point (the drawn
    // curve direction leaving the junction — what the eye reads as the meeting angle)
    const tdirs: number[] = []
    for (const leg of w.legs) {
      const atB = leg.b.kind === 'branch', atA = leg.a.kind === 'branch'
      if (!atA && !atB) continue
      const s = resolveLeg(e, w, leg)
      const pts: { x: number; y: number }[] = []
      traceLeg(s, pts, QN)
      const a = atB ? pts[pts.length - 1]! : pts[0]!, prev = atB ? pts[pts.length - 2]! : pts[1]!
      tdirs.push(Math.atan2(a.y - prev.y, a.x - prev.x))
    }
    expect(tdirs).toHaveLength(3)

    // PRINCIPLED TOLERANCE (not a magic number): the fixture is symmetric, so a
    // soap-film / Plateau energy model rests with every meeting angle EXACTLY 2π/3;
    // the only residual is the tangent-MEASUREMENT resolution of the QN-segment trace.
    // A leg's total turning is bounded by RANGE_B = π (loops unrepresentable), so its
    // QN=24 polyline turns at most π/QN ≈ 7.5° per segment and the final-segment chord
    // direction lags the true endpoint tangent by at most half that. A pairwise angle
    // sums the resolution of two legs, giving ≤ π/QN ≈ 7.5°. TOL = 2·(π/QN) = π/12 rad
    // (15°) allows that measurement floor plus the HX=0.02 finite-difference descent
    // resolution — while the trunk-tributary geometry the current model imposes deviates
    // by ~41° (measured 99.4°/99.4°/161.1°), failing this by nearly 3×.
    const TOL = (2 * Math.PI) / QN // = π/12 rad = 15°
    const target = (2 * Math.PI) / 3
    const P: [number, number][] = [[0, 1], [0, 2], [1, 2]]
    for (const [i, j] of P) {
      const ang = (between(tdirs[i]!, tdirs[j]!) * Math.PI) / 180
      expect(Math.abs(ang - target), `pair (${i},${j}) meets at ${((ang * 180) / Math.PI).toFixed(1)}°, not 120°`)
        .toBeLessThan(TOL)
    }
  })
})

describe('junction restructuring — a settled 4-way junction must reach the lower-energy Steiner topology', () => {
  it('settled total energy is no worse than the hand-built optimal pairing', () => {
    // Terminals pinned at the corners of a WIDE rectangle (0,1 = left pair; 2,3 =
    // right pair) so the optimal Steiner topology is unambiguous: pair the two LEFT
    // and the two RIGHT corners, (0,1)|(2,3), giving two branch points strung along
    // the long axis. The spiral seed makes buildJunctionTree choose (0,2)|(1,3)
    // instead (the top/bottom split), and no mover can restructure it.
    const corners = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]
    const pinAndSettle = (over: ((w: WireView) => void) | null): number => {
      const { d, b } = fourWay()
      const e = mkEngine(d, b)
      settle(e, 1) // establish scale + wire structure
      const ids = [...e.bodies.values()].filter((x) => x.kind === 'ref').map((x) => x.id)
      ids.forEach((id, n) => { const bod = e.bodies.get(id)!; bod.pos = { ...corners[n]! }; bod.theta = 0 })
      const w = [...e.wires.values()].find((x) => x.binds.length === 4)!
      if (over !== null) over(w)
      e.frame = null // re-establish a frame that FITS the pinned rectangle
      const pinned = new Set(ids)
      for (let t = 0; t < 4000; t++) { if (!settleStep(e, pinned)) break } // fixed-point settle, hard cap
      return totalEnergy(e)
    }

    // the frozen system: seeded (0,2)|(1,3) topology, terminals pinned at the rectangle
    const eSeeded = pinAndSettle(null)
    // the hand-built optimal topology on the SAME pinned geometry
    const eOptimal = pinAndSettle((w) => setPairing(w, 0, 1, 2, 3, corners))

    // A junction paradigm that minimizes energy over topology as well as position must
    // not rest at a topology strictly worse than a reachable alternative. FLOAT_NOISE is
    // the fixed-point settle's own residual (a few tenths of an energy unit); the gap
    // here is ~3× (measured seeded ≈ 496 vs optimal ≈ 165), so any small noise bound
    // fails the same way. Passes only once restructuring lets the seed flip to (0,1)|(2,3).
    const FLOAT_NOISE = 1.0
    expect(eSeeded, `seeded topology settled to E=${eSeeded.toFixed(1)}, optimal E=${eOptimal.toFixed(1)} — the frozen tree never restructures`)
      .toBeLessThanOrEqual(eOptimal + FLOAT_NOISE)
  })
})
