import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg, traceLeg, type WireView } from '../../src/view/engine'
import { settle, totalEnergy } from '../../src/view/relax'
import { QN, thetaRange } from '../../src/view/elastica'

/**
 * JUNCTION EQUILIBRATION (law test).
 *
 * A settled symmetric triple junction must be a STRICT LOCAL MINIMUM of the total
 * energy over its branch position and its free leg tangents, with every leg
 * REPRESENTABLE (tangent range < π — kinks unrepresentable at the branch). This is
 * the physics law, not an aesthetic: no specific meeting angle is asserted (the
 * junction LOOK is left to the gallery ruling).
 *
 * Junction RESTRUCTURING is NOT tested here: whether static descent from a pinned
 * seed REACHES a lower-energy topology is a reachability-of-faces claim, which the
 * accepted semantics disavow (2026-07-23: "resting in a local minimum is legitimate;
 * restructuring is something the user's manipulation drives through continuous
 * passages, not something the system seeks") and which is Task 3's measurement. The
 * face-crossing MECHANISM (φ carries T across ℓ_e = 0 under the strict gate) is
 * exercised in junction-crossing.test.ts.
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

/** The direction of a branch leg's drawn curve AT the branch point — what the eye
    reads as the meeting angle (used only for the smoothness/representability law,
    never to assert a specific angle, which the user has not ruled). */
function branchLegDirs(e: ReturnType<typeof mkEngine>, w: WireView, bi: number): number[] {
  const dirs: number[] = []
  for (const leg of w.legs) {
    const atB = leg.b.kind === 'branch' && leg.b.i === bi
    const atA = leg.a.kind === 'branch' && leg.a.i === bi
    if (!atA && !atB) continue
    const s = resolveLeg(e, w, leg)
    const pts: { x: number; y: number }[] = []
    traceLeg(s, pts, QN)
    const a = atB ? pts[pts.length - 1]! : pts[0]!, prev = atB ? pts[pts.length - 2]! : pts[1]!
    dirs.push(Math.atan2(a.y - prev.y, a.x - prev.x))
  }
  return dirs
}

/**
 * The energy-law replacements for the DELETED 120°-asserting test. The user has NOT
 * ruled that a symmetric junction must meet at 120° (the corpus explicitly leaves the
 * junction LOOK to a visual ruling — see the gallery). So we assert only what IS law:
 *  (i)  the settled junction is a STRICT LOCAL MINIMUM of the total energy over its
 *       branch position AND its free leg tangents — the physics, not an aesthetic;
 *  (ii) every leg at the junction is REPRESENTABLE (tangent range < π), i.e. kinks are
 *       unrepresentable AT the branch, the founding smoothness law.
 */
describe('junction equilibration — a settled symmetric triple is a strict energy minimum with smooth legs', () => {
  it('no branch-position or tangent perturbation lowers the total energy (strict local minimum)', () => {
    const { d, b } = symTriple()
    const e = mkEngine(d, b)
    settle(e, 8000) // fixed-point settle, hard cap (repo idiom; converges in <300 ticks)
    const w = [...e.wires.values()].find((x) => x.branches.length > 0)!
    expect(w.branches, 'the symmetric triple is a one-branch Steiner tree').toHaveLength(1)
    const E0 = totalEnergy(e)
    // float-noise floor on a strict-minimum probe: the descent rests where no gated
    // step improves at resolution HX=0.02, so a genuine minimum shows deltaE ≥ 0 up to
    // that residual. A trunk-clamped saddle (the old defect) would show a probe well
    // below E0; this discriminates cleanly.
    const NOISE = 1e-4 * (Math.abs(E0) + 1)
    const sc = e.scale

    // (i-a) branch POSITION grid probe (the diagnosis pattern): every neighbour on a
    // ±3·scale grid must be no lower than the settled point.
    const b0 = { ...w.branches[0]! }
    let minPos = 0
    for (let ix = -3; ix <= 3; ix++) for (let iy = -3; iy <= 3; iy++) {
      if (ix === 0 && iy === 0) continue
      w.branches[0] = { x: b0.x + ix * sc, y: b0.y + iy * sc }
      minPos = Math.min(minPos, totalEnergy(e) - E0)
    }
    w.branches[0] = b0
    expect(minPos, `a branch-position perturbation lowered E by ${(-minPos).toFixed(4)} — not a local min`).toBeGreaterThanOrEqual(-NOISE)

    // (i-b) TANGENT probe: perturbing any branch-incident leg's arrival tangent (angB)
    // must not lower the energy either.
    let minTan = 0
    for (const leg of w.legs) {
      if (leg.b.kind !== 'branch') continue
      const a0 = leg.angB
      for (const d2 of [-0.3, -0.15, -0.05, 0.05, 0.15, 0.3]) {
        leg.angB = a0 + d2
        minTan = Math.min(minTan, totalEnergy(e) - E0)
      }
      leg.angB = a0
    }
    expect(minTan, `a leg-tangent perturbation lowered E by ${(-minTan).toFixed(4)} — not a local min`).toBeGreaterThanOrEqual(-NOISE)
  })

  it('every leg at the junction is representable (tangent range < π): kinks are unrepresentable at the branch', () => {
    const { d, b } = symTriple()
    const e = mkEngine(d, b)
    settle(e, 8000)
    const w = [...e.wires.values()].find((x) => x.branches.length > 0)!
    for (const leg of w.legs) {
      const s = resolveLeg(e, w, leg)
      const rng = Math.abs(thetaRange(s.sol.c1, s.sol.c2))
      expect(rng, `a junction leg has tangent range ${(rng / Math.PI).toFixed(2)}π ≥ π (a kink/wrap)`).toBeLessThan(Math.PI)
    }
    // and the three meeting directions are genuinely distinct (a real Y-junction, not
    // all three legs collapsed onto one line — the "everything to a single point" the
    // user rejected). No specific angle is asserted.
    const dirs = branchLegDirs(e, w, 0)
    expect(dirs).toHaveLength(3)
    let minSep = 360
    for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) minSep = Math.min(minSep, between(dirs[i]!, dirs[j]!))
    expect(minSep, `two legs meet at only ${minSep.toFixed(0)}° — the junction collapsed toward a single line`).toBeGreaterThan(20)
  })
})
