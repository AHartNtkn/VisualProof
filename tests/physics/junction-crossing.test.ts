import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { mkEngine, resolveLeg, traceLeg } from '../../src/view/engine'
import type { Engine, WireView, WireLeg, WireLegEnd } from '../../src/view/engine'
import { settleStep, totalEnergy, recomputeRegions, establishFrame } from '../../src/view/relax'
import { QN, mkLegCache, legCache } from '../../src/view/elastica'

/**
 * FACE CROSSING (stratified junctions, phi-construction §1, §4): the branch-position DOF
 * carries the wire's topology T across a stratum boundary (ℓ_e = 0) via the canonical
 * transition φ, under the ordinary strict-descent gate — no trigger, no throttle, no
 * separate topology mover. These are MECHANISM reproductions: a crossing is ACCEPTED when
 * the state is at a face (branches within the drawing-resolution window) and a re-paired
 * chart strictly lowers E, REFUSED when the current chart is already lowest, the drawing
 * is φ-identical across the face (Lemma 2), and the trajectory is deterministic.
 *
 * These do NOT assert reachability-of-faces (whether descent DRIVES a given seed to a
 * face) — that is Task 3's measurement, out of scope here. The states are constructed AT
 * the face and the φ decision is exercised directly.
 *
 * The fixture is a 4-way junction (two branch points, one internal edge) whose four
 * terminals sit at a WIDE rectangle's corners — a clean, well-spaced geometry where each
 * pairing's terminal centroids are DISTINCT from the merge point, so every chart has a
 * genuine φ re-expansion direction (unlike a degenerate colinear/coincident-centroid
 * fixture, where all charts re-expand to the same point and the crossing signal vanishes
 * into the clearance energy). The drawing-resolution merge window is 0.01 wu (the elastica
 * L≥0.01 floor, phi-construction Fact 0.1) — MERGE_EPS in relax.ts.
 */

const MERGE_EPS = 0.01 // relax.ts drawing-resolution window (phi-construction Fact 0.1)
const rel = (n: number): ReturnType<typeof relSig> => relSig(Array.from({ length: n }, () => TERM))

/** Four unary-wired refs sharing one 4-way line of identity (two branch points). */
function fourWay(): Diagram {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'a', rel(3)); const r2 = b.ref(b.root, 'bb', rel(3))
  const r3 = b.ref(b.root, 'cc', rel(3)); const r4 = b.ref(b.root, 'dd', rel(3))
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } }, { node: r2, port: { kind: 'arg', index: 0 } },
    { node: r3, port: { kind: 'arg', index: 0 } }, { node: r4, port: { kind: 'arg', index: 0 } },
  ])
  return b.build()
}

// A WIDE rectangle: left column {0,1}, right column {2,3}. Well-spaced (disc radius ≈ 7,
// nearest same-column pair 24 apart) so the terminal legs are clean and low-energy.
const WIDE: { x: number; y: number }[] = [{ x: -40, y: -12 }, { x: -40, y: 12 }, { x: 40, y: -12 }, { x: 40, y: 12 }]

/** Impose pairing (i,j)|(k,l): B0 groups i,j and B1 groups k,l, placed at the two
    branch positions `b0,b1`, every leg tangent seeded to its chord direction (a straight
    leg). With b0,b1 within MERGE_EPS the wire is AT the face (its stub invisible). */
function setPairing(w: WireView, i: number, j: number, k: number, l: number, c: readonly { x: number; y: number }[], b0: { x: number; y: number }, b1: { x: number; y: number }): void {
  const bind = (n: number): WireLegEnd => ({ kind: 'bind', i: n })
  const br = (n: number): WireLegEnd => ({ kind: 'branch', i: n })
  const chord = (f: { x: number; y: number }, t: { x: number; y: number }): number => Math.atan2(t.y - f.y, t.x - f.x)
  const mk = (a: WireLegEnd, bb: WireLegEnd, f: { x: number; y: number }, t: { x: number; y: number }): WireLeg => ({ a, b: bb, angA: chord(f, t), angB: chord(f, t), cache: mkLegCache() })
  w.branches.length = 0; w.branches.push({ ...b0 }, { ...b1 })
  w.legs.length = 0
  for (const lg of [
    mk(bind(i), br(0), c[i]!, b0), mk(bind(j), br(0), c[j]!, b0),
    mk(bind(k), br(1), c[k]!, b1), mk(bind(l), br(1), c[l]!, b1),
    mk(br(0), br(1), b0, b1),
  ]) w.legs.push(lg)
}

/** The unordered set of terminal-pairs sharing a branch — the wire's TOPOLOGY T, e.g.
    "01|23". Order-independent, so it identifies the pairing regardless of branch labelling. */
function pairing(w: WireView): string {
  const per = new Map<number, number[]>()
  for (const leg of w.legs) {
    let br = -1, term = -1
    for (const end of [leg.a, leg.b]) { if (end.kind === 'branch') br = end.i; if (end.kind === 'bind') term = end.i }
    if (br >= 0 && term >= 0) { const a = per.get(br) ?? []; a.push(term); per.set(br, a) }
  }
  return [...per.values()].map((a) => a.sort().join('')).sort().join('|')
}

/** Branch separation ℓ_e (world units). */
function branchGap(w: WireView): number {
  return Math.hypot(w.branches[0]!.x - w.branches[1]!.x, w.branches[0]!.y - w.branches[1]!.y)
}

/** The DRAWING of a wire as a sorted point cloud of every leg's traced samples (D_T). */
function drawingCloud(e: Engine, w: WireView): { x: number; y: number }[] {
  const pts: { x: number; y: number }[] = []
  for (const leg of w.legs) {
    const s = resolveLeg(e, w, leg)
    const out: { x: number; y: number }[] = []
    traceLeg(s, out, QN)
    for (const p of out) pts.push(p)
  }
  return pts.sort((a, b) => a.x - b.x || a.y - b.y)
}

/** Directed Hausdorff distance from cloud A to cloud B (max over A of nearest-in-B). */
function hausdorff(a: readonly { x: number; y: number }[], b: readonly { x: number; y: number }[]): number {
  let worst = 0
  for (const p of a) {
    let best = Infinity
    for (const q of b) { const d = Math.hypot(p.x - q.x, p.y - q.y); if (d < best) best = d }
    worst = Math.max(worst, best)
  }
  return worst
}

/** Build a wide-rect fourWay engine, pin the refs at the corners FACING the junction
    centroid, force `pair` with its branches at `b0,b1`, and establish the frame directly
    from the pinned geometry — no descent sweep, so a near-face seed is observed on the
    first sweep. */
function pinnedWide(pair: [number, number, number, number], b0: { x: number; y: number }, b1: { x: number; y: number }): { e: Engine; w: WireView; pinned: Set<string> } {
  const e = mkEngine(fourWay(), [] as readonly WireId[])
  const w = [...e.wires.values()].find((x) => x.binds.length === 4)!
  const pinned = new Set<string>()
  w.binds.forEach((bd, n) => {
    const b = e.bodies.get(bd.body)!
    b.pos = { ...WIDE[n]! }
    const la = b.localAnchor.get(bd.key)!
    b.theta = Math.atan2(-b.pos.y, -b.pos.x) - Math.atan2(la.y, la.x) // wired port faces the origin (junction centroid)
    pinned.add(bd.body)
  })
  setPairing(w, pair[0], pair[1], pair[2], pair[3], WIDE, b0, b1)
  recomputeRegions(e)
  establishFrame(e)
  return { e, w, pinned }
}

// A near-face seed just inside the merge window, split along a rectangle axis.
const NEAR = MERGE_EPS * 0.6 // 0.006 < MERGE_EPS

describe('face crossing — accepted when a re-paired chart strictly lowers E, refused otherwise', () => {
  it('a suboptimal chart at the face crosses to a strictly-lower pairing under strict descent', () => {
    // 03|12 pairs the DIAGONAL corners of the wide rect — a high-energy chart. At the face
    // the gated φ move crosses to a strictly-lower pairing (02|13, the row split). This is
    // ONE test of the whole gate law: a beneficial crossing IS taken (accept), no crossing
    // ever RAISES the total energy (refuse-of-any-E-raising move — the ratified strict-
    // descent paradigm), and the result is a settled representable junction. It does NOT
    // assert WHICH basin is reached from a static seed (reachability — Task 3's scope).
    const { e, w, pinned } = pinnedWide([0, 3, 1, 2], { x: -NEAR / 2, y: 0 }, { x: NEAR / 2, y: 0 })
    expect(pairing(w)).toBe('03|12')
    expect(branchGap(w), 'seed starts at the face (within the merge window)').toBeLessThan(MERGE_EPS)
    const start = pairing(w)
    let crossed = false, worstRise = 0
    let prevE = totalEnergy(e)
    for (let t = 0; t < 800; t++) {
      const p0 = pairing(w)
      const moved = settleStep(e, pinned)
      const curE = totalEnergy(e)
      worstRise = Math.max(worstRise, curE - prevE)
      prevE = curE
      if (pairing(w) !== p0) crossed = true
      if (!moved) break
    }
    expect(crossed, 'the wire never crossed the ℓ_e = 0 face').toBe(true)
    expect(pairing(w), 'the crossing must leave the diagonal chart for a lower one').not.toBe(start)
    // STRICT DESCENT (the gate's law, and the "refuse when it would not lower E" guarantee):
    // total energy is monotone non-increasing across every sweep — no crossing ever raised it.
    expect(worstRise, `total energy rose by ${worstRise.toFixed(3)} across a sweep (strict descent / gate violated)`).toBeLessThan(1e-6 * (Math.abs(prevE) + 1))
    // and it rests in a settled, representable junction (no leg wraps)
    for (const leg of w.legs) {
      const s = resolveLeg(e, w, leg)
      expect(Math.abs(s.sol.c1 + s.sol.c2), 'a leg wraps at the crossed rest').toBeLessThan(Math.PI * 2)
    }
  })
})

describe('face crossing — the drawing is φ-identical across the face (Lemma 2)', () => {
  it('two NNI-related charts at the same face draw the same picture up to solver resolution', () => {
    // At a face (branches within MERGE_EPS at the same merge point m) the current chart
    // and its NNI re-pairing draw the IDENTICAL picture: φ carries the four surviving
    // legs' tangents unchanged and the collapsed edge is an invisible ≤MERGE_EPS stub.
    // This is the guarantee that makes a crossing a continuous passage — tested directly,
    // isolated from the node-rotation DOF that also moves on a live crossing sweep.
    const m = { x: 0, y: 0 }
    const h = MERGE_EPS / 2

    const a = pinnedWide([0, 1, 2, 3], { x: m.x - h, y: m.y }, { x: m.x + h, y: m.y })
    const before = drawingCloud(a.e, a.w)

    // the NNI re-pairing 02|13 at the SAME face (same m), tangents carried by the same
    // chord construction (identity on the intrinsic data at m)
    const b = pinnedWide([0, 2, 1, 3], { x: m.x, y: m.y - h }, { x: m.x, y: m.y + h })
    const after = drawingCloud(b.e, b.w)

    const d = Math.max(hausdorff(before, after), hausdorff(after, before))
    // Lemma 2 (phi-construction §1.3) holds "up to solver resolution": the four surviving
    // arcs are identical by Fact 0.3, and the collapsed edge's stub is <=0.01-diameter
    // (Fact 0.1, elastica.ts's L>=0.01 floor) — invisible at that scale, which is exactly
    // MERGE_EPS (relax.ts), the drawing-resolution window this whole face mechanism is
    // built on (§4.2: "MERGE_EPS = the drawing resolution (0.01, Fact 0.1)"). The bound is
    // that resolution itself, not an arbitrary tolerance.
    expect(d, `two charts at the face drew pictures ${d.toFixed(3)} wu apart (Lemma 2 violated)`).toBeLessThan(MERGE_EPS)
  })
})

describe('face crossing — deterministic trajectory (leg cache on/off)', () => {
  function trajectorySnapshot(withCache: boolean): number[] {
    const prev = legCache.enabled
    try {
      legCache.enabled = withCache
      const { e, w, pinned } = pinnedWide([0, 1, 2, 3], { x: -NEAR / 2, y: 0 }, { x: NEAR / 2, y: 0 })
      for (let t = 0; t < 300; t++) if (!settleStep(e, pinned)) break
      const out: number[] = []
      for (const b of e.bodies.values()) out.push(b.pos.x, b.pos.y, b.theta)
      for (const leg of w.legs) out.push(leg.angA, leg.angB)
      for (const bp of w.branches) out.push(bp.x, bp.y)
      out.push(pairing(w).length) // topology reached (encoded)
      return out
    } finally { legCache.enabled = prev }
  }
  it('the same trajectory is bit-identical across two runs', () => {
    const a = trajectorySnapshot(true), b = trajectorySnapshot(true)
    expect(a.length).toBe(b.length)
    let maxd = 0
    for (let i = 0; i < a.length; i++) maxd = Math.max(maxd, Math.abs(a[i]! - b[i]!))
    expect(maxd, `two identical runs diverged by ${maxd} — non-determinism`).toBe(0)
  })
  it('the crossing trajectory is identical with the leg-solve cache on vs off', () => {
    const on = trajectorySnapshot(true), off = trajectorySnapshot(false)
    expect(off.length).toBe(on.length)
    let maxd = 0
    for (let i = 0; i < on.length; i++) maxd = Math.max(maxd, Math.abs(on[i]! - off[i]!))
    expect(maxd, `the cache changed the crossing trajectory by ${maxd} (must be 0 — a pure memo)`).toBe(0)
  })
})
