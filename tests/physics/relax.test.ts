import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig } from '../../src/kernel/diagram/sig'
import { carryOver, mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { settle, settleStep, totalEnergy, clampDragToFeasible, seedProject, establishProofFrame, recomputeRegions, resolveOverlaps, establishFrame } from '../../src/view/relax'
import {
  commutedBoundaryRefs,
  identityJunctionScene,
  identityRefScene,
  unaryDefinition,
  UNARY,
} from '../fixtures/zero-signature'

const sentence = relSig([])
const commuted = commutedBoundaryRefs()
const unary = unaryDefinition()

const cases: [string, Diagram, readonly WireId[]][] = [
  ['commuted.rhs', commuted.rhs.diagram, commuted.rhs.boundary],
  ['unaryDefinition', unary.diagram, unary.boundary],
  ['identityJunction', identityJunctionScene(), []],
]

// Every READ-ONLY law assertion below (containment, disc-in-frame, port facing, no
// leg wraps) needs a SETTLED fixture, and settling a framed fixture is the dominant
// test cost. Settle each case ONCE and share the resting engine across all of those
// assertions — they only READ it, never mutate, so sharing changes WHEN the engine
// is built, never WHAT is asserted. Tests that MUTATE after settling (the frame-
// breathe run, drag clamp, twist, angular-speed knock) keep their OWN engines. The
// shared cap 1100 is the highest budget any of these read-only tests used; the plan-
// 24 fixed-point stop terminates well under it for the converging fixtures.
const settledShared = new Map<string, Engine>()
function settledCase(name: string, d: Diagram, boundary: readonly WireId[]): Engine {
  let e = settledShared.get(name)
  if (e === undefined) {
    e = mkEngine(d, boundary)
    if (!settleWithin(e, 20_000)) throw new Error(`${name}: did not rest within 20 s`)
    settledShared.set(name, e)
  }
  return e
}

/** Two circles are legal iff disjoint or one strictly contains the other. */
function partiallyOverlaps(a: { center: { x: number; y: number }; radius: number }, b: { center: { x: number; y: number }; radius: number }): boolean {
  const dist = Math.hypot(a.center.x - b.center.x, a.center.y - b.center.y)
  const EPS = 0.5
  const disjoint = dist >= a.radius + b.radius - EPS
  const nested = dist + Math.min(a.radius, b.radius) <= Math.max(a.radius, b.radius) + EPS
  return !(disjoint || nested)
}

function anyOverlap(e: { regions: Map<string, { center: { x: number; y: number }; radius: number }> }): boolean {
  const rs = [...e.regions.values()]
  for (let i = 0; i < rs.length; i++) {
    for (let j = i + 1; j < rs.length; j++) {
      if (partiallyOverlaps(rs[i]!, rs[j]!)) return true
    }
  }
  return false
}

/**
 * The plan-23 strict-descent contract on a settled fixture, all four properties
 * from ONE settle (each framed settle is expensive):
 *   (a) ANCHORED — every body inside the trivial packing bound (no runaway).
 *   (b) LEGAL — no two region circles partially intersect (the USER hard law).
 *   (c) RESTS — max body drift over 200 further ticks ≤ `driftBound` (settle-and-
 *       stay). Bounds RE-DERIVED from THIS model's measured drift (USER policy),
 *       measured 2026-07-06: ~0.0 on every fixture; pinned at 1.5 with margin.
 *   (d) MONOTONE — total energy is non-increasing across every one of those 200
 *       post-settle ticks (the USER's "the system does not change if it doesn't
 *       lower energy", now a THEOREM of the one-gated-mover architecture; measured
 *       post-settle max single-step rise 0.0000, pinned at 1e-3 for float noise).
 *       This is the pin that catches any un-gated mover sneaking back in — a limit
 *       cycle shows as a sustained rise. (It is asserted at rest, where the derived
 *       enclosing-circle/frame geometry is stationary; during the seed transient a
 *       minimal-enclosing-circle support switch is a legitimate re-fit, not a
 *       mover, so strict per-step monotonicity there is not the claim.)
 */
/** Settle to the operator's proven rest within a WALL-CLOCK budget (USER ruling
    2026-07-24: a physics test settles within its budget or FAILS — vitest's
    timeout cannot interrupt a synchronous loop, so the clock lives here). */
function settleWithin(e: Engine, maxMs: number): boolean {
  // the same bracketing as `settle`: leading legality projection + frame
  // establishment, wall-clock-bounded descent, trailing projection
  recomputeRegions(e)
  resolveOverlaps(e)
  establishFrame(e)
  const t0 = performance.now()
  let rested = false
  for (;;) {
    if (!settleStep(e)) { rested = true; break }
    if (performance.now() - t0 > maxMs) break
  }
  recomputeRegions(e)
  resolveOverlaps(e)
  return rested
}


describe('settle stops at a proven fixed point (plan-24 perf — no wasted budget)', () => {
  // The strict-descent mover is deterministic, strictly value-gated (a DOF commits a
  // move only at a strictly LOWER energy), and its proposals depend ONLY on current
  // state — the DOF worklist is rebuilt each sweep from positions, with no tick
  // index, no stored per-DOF scale, and no randomness. So a sweep that accepts zero
  // moves leaves the state BIT-IDENTICAL, and the next sweep rebuilds the same
  // worklist over the same state and again moves nothing: it is a proven fixed point,
  // and stopping there is identical to burning the whole budget. `settle` now takes
  // `ticks` as a CAP and returns the ticks actually run.
  const twoNodes = (): { d: Diagram; b: readonly WireId[] } => {
    const h = new DiagramBuilder()
    h.ref(h.root, 'A', sentence)
    h.ref(h.root, 'B', sentence)
    return { d: h.build(), b: [] }
  }
  const snap = (e: Engine): number[] => [...e.bodies.values()].flatMap((b) => [b.pos.x, b.pos.y, b.theta])

  it('a settling diagram stops far short of the cap and rests exactly there', () => {
    const { d, b } = twoNodes()
    const e = mkEngine(d, b)
    const cap = 20000
    const used = settle(e, cap)
    expect(used, `settle burned the whole ${cap}-tick budget — the fixed-point stop never fired`).toBeLessThan(cap)
    expect(used, 'two floating nodes rest quickly; a large tick count means the stop is late').toBeLessThan(500)
    // proven fixed point: 50 further sweeps must change NOTHING (bit-identical)
    const s0 = snap(e)
    for (let i = 0; i < 50; i++) settleStep(e)
    const s1 = snap(e)
    let maxd = 0
    for (let i = 0; i < s0.length; i++) maxd = Math.max(maxd, Math.abs(s0[i]! - s1[i]!))
    expect(maxd, `state drifted ${maxd} over 50 post-stop ticks — the stop was not a true fixed point`).toBe(0)
  })

  it('re-settling an already-settled diagram stops after a single sweep', () => {
    const { d, b } = twoNodes()
    const e = mkEngine(d, b)
    settle(e, 20000)
    const again = settle(e, 20000)
    expect(again, 'a settled diagram must detect the fixed point on the first re-settle sweep').toBe(1)
  })

  it('early-stop settle is BIT-IDENTICAL to burning the full tick budget', () => {
    // Full-budget reference: the SAME leading construction projection settle applies
    // (recomputeRegions + resolveOverlaps + establishFrame; the branch re-seed is a
    // no-op here — no boundary Steiner wires), then a FIXED settleStep loop with no
    // early stop, then the same trailing projection.
    const { d, b } = twoNodes()
    const N = 4000
    const ref = mkEngine(d, b)
    recomputeRegions(ref); resolveOverlaps(ref); establishFrame(ref)
    for (let t = 0; t < N; t++) settleStep(ref)
    recomputeRegions(ref); resolveOverlaps(ref)

    const es = mkEngine(d, b)
    const used = settle(es, N)
    expect(used, 'early stop should fire well within the budget').toBeLessThan(N)

    const r = snap(ref), s = snap(es)
    expect(s.length).toBe(r.length)
    let maxd = 0
    for (let i = 0; i < r.length; i++) maxd = Math.max(maxd, Math.abs(r[i]! - s[i]!))
    expect(maxd, `early-stop layout differs from the full-budget layout by ${maxd} (must be exactly 0)`).toBe(0)
  })
})

describe('law 1 — containment: no two region circles ever intersect', () => {
  for (const [name, d, boundary] of cases) {
    it(`holds after settle for ${name}`, () => {
      const e = settledCase(name, d, boundary)
      expect(anyOverlap(e), `regions overlap in ${name}`).toBe(false)
    })
  }

  // The legality STRESS case: ten sibling cuts pulled together by cohesion. Under
  // plan 23 the UNCAPPED sibling barrier (sibU) dominates that pull, so the strict
  // descent rests them disjoint on its own, and `settle`'s construction-time
  // projection is the discrete-event backstop for any externally-constructed
  // overlap. Either way the drawing must be legal at rest.
  it('holds for a dense sheet of sibling cuts', () => {
    const h = new DiagramBuilder()
    for (let c = 0; c < 10; c++) {
      const cut = h.cut(h.root)
      for (let i = 0; i < 3; i++) h.ref(cut, `R${c}-${i}`, sentence)
    }
    const e = mkEngine(h.build(), [])
    settle(e, 1100)
    expect(anyOverlap(e), 'dense sibling cuts must not partially overlap').toBe(false)
  })
})




describe('the fixed near-square frame (plan 24, USER RULING 2026-07-06)', () => {
  // The frame is ABSOLUTE state set once at establishment and CONSTANT between
  // rewrites — it never grows/shrinks/shifts from motion. A HARD edge the content
  // lives within: a settling trial or a drag past the inner edge is projected back.
  it('the frame is byte-identical across 500 settle ticks — it never breathes', () => {
    for (const [name, diagram, boundary] of cases) {
      const e = mkEngine(diagram, boundary)
      settle(e, 300) // establishes the frame from the legal seed, settles to rest
      const f0 = e.frame
      expect(f0, `${name}: frame must be established after settle`).not.toBeNull()
      const snap = JSON.stringify(f0)
      for (let t = 0; t < 500; t++) settleStep(e)
      expect(JSON.stringify(e.frame), `${name}: frame breathed during settling`).toBe(snap)
    }
  })

  it('every content disc rests INSIDE the fixed frame (the hard edge holds it in)', () => {
    for (const [name, diagram, boundary] of cases) {
      const e = settledCase(name, diagram, boundary)
      const f = e.frame!
      for (const b of e.bodies.values()) {
        if (b.id.startsWith('e:')) continue // frame terminals ride ON the edge
        const over = Math.max(Math.abs(b.pos.x - f.center.x), Math.abs(b.pos.y - f.center.y)) + b.discR - f.half
        expect(over, `${name}: body ${b.id} pokes ${over.toFixed(3)} wu past the frame`).toBeLessThanOrEqual(0.5)
      }
    }
  })

  it('a drag toward the edge is clamped inside and NEVER grows the frame', () => {
    for (const [name, diagram, boundary] of cases) {
      const e = mkEngine(diagram, boundary)
      settle(e, 300)
      const f = e.frame!
      const half0 = f.half
      const node = [...e.bodies.values()].find((b) =>
        b.kind === 'ref' || b.kind === 'atom' || b.kind === 'identity')!
      // a wild cursor target far outside every edge, in all four diagonal directions
      for (const [sx, sy] of [[1, 1], [-1, 1], [1, -1], [-1, -1]] as const) {
        const clamped = clampDragToFeasible(e, node, { x: f.center.x + sx * 1e4, y: f.center.y + sy * 1e4 })
        const over = Math.max(Math.abs(clamped.x - f.center.x), Math.abs(clamped.y - f.center.y)) + node.discR - f.half
        expect(over, `${name}: drag (${sx},${sy}) clamped ${over.toFixed(3)} past the edge`).toBeLessThanOrEqual(0.5)
      }
      expect(e.frame!.half, `${name}: the drag grew the frame`).toBe(half0)
    }
  })
})

describe('content-fill scaling — a step is sized to the fixed border (plan 24, USER RULING 2026-07-07)', () => {
  // The border is fixed proof-wide; each step's CONTENT is scaled in either
  // direction (one uniform Engine.scale) so it FILLS the border instead of
  // rendering tiny or overflowing. The seed path (app seedProject): proof-wide
  // frame, then applyContentScale sizes THIS step.
  const steps = [
    unaryDefinition(),
    { diagram: identityRefScene(), boundary: [] },
  ]
  // one fixed proof-wide frame, established once (as enterReplay does)
  const probe = mkEngine(steps[0]!.diagram, steps[0]!.boundary)
  establishProofFrame(probe, steps)
  const frame = probe.frame!

  // build a step through the app seed path and settle it
  const seedStep = (k: number, ticks: number): Engine => {
    const step = steps[k]!
    const e = mkEngine(step.diagram, step.boundary)
    e.frame = frame
    seedProject(e)
    settle(e, ticks)
    return e
  }
  // BOX half-extent (the frame is a near-square, not a circle): the max per-axis
  // reach from the frame centre. A disc in a corner is inside the box even though
  // its RADIAL distance exceeds the half — measure the wall the clamp enforces.
  const contentHalf = (e: Engine): number => {
    const ownFrame = e.frame!
    let h = 0
    const box = (cx: number, cy: number, r: number): void => { h = Math.max(h, Math.abs(cx - ownFrame.center.x) + r, Math.abs(cy - ownFrame.center.y) + r) }
    for (const b of e.bodies.values()) { if (b.id.startsWith('e:')) continue; box(b.pos.x, b.pos.y, b.discR * e.scale) }
    for (const [rid, g] of e.regions) { if (rid === e.d.root) continue; box(g.center.x, g.center.y, g.radius) }
    return h
  }

  // A SMALL step (few nodes) must fill the fixed border, not render tiny. Measured
  // Occupancy must remain substantial across sparse and identity-rich steps. It
  // must not spill past the border.
  for (const k of [0, steps.length - 1]) {
    it(`small step ${k} fills the border (occupancy in band) and stays inside`, () => {
      const e = seedStep(k, 700)
      const occ = contentHalf(e) / frame.half
      expect(Number.isFinite(e.scale) && e.scale > 0, `step ${k}: content scale must be finite and positive`).toBe(true)
      expect(occ, `step ${k}: content fills only ${(occ * 100).toFixed(0)}% of the border — too tiny`).toBeGreaterThan(0.6)
      expect(occ, `step ${k}: content spills past the border (${(occ * 100).toFixed(0)}%)`).toBeLessThanOrEqual(1.02)
    })
  }

  it('one sparse→dense lifecycle keeps the frame exact and uniformly scales content in both directions', () => {
    const sparseBuilder = new DiagramBuilder()
    sparseBuilder.ref(sparseBuilder.root, 'Stable', sentence)
    const sparse = mkEngine(sparseBuilder.build(), [])
    seedProject(sparse)
    const frameSnapshot = JSON.stringify(sparse.frame)
    const lifecycleFrame = sparse.frame!

    const denseBuilder = new DiagramBuilder()
    denseBuilder.ref(denseBuilder.root, 'Stable', sentence) // n0 survives the rewrite
    for (let c = 0; c < 8; c++) {
      const cut = denseBuilder.cut(denseBuilder.root)
      for (let i = 0; i < 6; i++) denseBuilder.ref(cut, `D${c}-${i}`, sentence)
    }
    const dense = mkEngine(denseBuilder.build(), [])
    carryOver(sparse, dense)
    seedProject(dense)

    expect(JSON.stringify(dense.frame), 'content growth changed the stored frame').toBe(frameSnapshot)
    expect(Number.isFinite(sparse.scale) && sparse.scale > 0, 'sparse scale must be finite and positive').toBe(true)
    expect(Number.isFinite(dense.scale) && dense.scale > 0, 'dense scale must be finite and positive').toBe(true)
    expect(dense.scale, 'dense content must use a lower ratio than sparse content').toBeLessThan(sparse.scale)
    expect(dense.scale, 'sufficiently dense content must shrink below natural size').toBeLessThan(1)

    for (const [label, e] of [['sparse', sparse], ['dense', dense]] as const) {
      const occ = contentHalf(e) / lifecycleFrame.half
      expect(occ, `${label}: content fills only ${(occ * 100).toFixed(0)}% of the fixed frame`).toBeGreaterThan(0.6)
      expect(occ, `${label}: content spills past the fixed frame (${(occ * 100).toFixed(0)}%)`).toBeLessThanOrEqual(1.02)
      expect(anyOverlap(e), `${label}: scaling broke region legality`).toBe(false)
      for (const b of e.bodies.values()) {
        if (b.id.startsWith('e:')) continue
        const over = Math.max(Math.abs(b.pos.x - lifecycleFrame.center.x), Math.abs(b.pos.y - lifecycleFrame.center.y)) + b.discR * e.scale - lifecycleFrame.half
        expect(over, `${label}: body ${b.id} pokes ${over.toFixed(3)} wu past the fixed frame`).toBeLessThanOrEqual(0.5)
      }
    }
  })

  it('uniform scaling and carry-over preserve Steiner branch geometry', () => {
    const h = new DiagramBuilder()
    const a = h.ref(h.root, 'A', UNARY)
    const b = h.ref(h.root, 'B', UNARY)
    const c = h.ref(h.root, 'C', UNARY)
    const wire = h.wire(h.root, [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: b, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = h.build()
    const first = mkEngine(diagram, [])
    seedProject(first)
    const firstBranch = { ...first.wires.get(wire)!.net.junctions[0]! }
    expect(first.wires.get(wire)!.net.junctions).toHaveLength(1)

    const rebuilt = mkEngine(diagram, [])
    carryOver(first, rebuilt)
    seedProject(rebuilt)
    const rebuiltBranch = rebuilt.wires.get(wire)!.net.junctions[0]!

    expect(rebuilt.scale).toBeCloseTo(first.scale, 10)
    expect(rebuiltBranch.x).toBeCloseTo(firstBranch.x, 8)
    expect(rebuiltBranch.y).toBeCloseTo(firstBranch.y, 8)
    const frame = rebuilt.frame!
    expect(Math.abs(rebuiltBranch.x - frame.center.x)).toBeLessThanOrEqual(frame.half)
    expect(Math.abs(rebuiltBranch.y - frame.center.y)).toBeLessThanOrEqual(frame.half)
  })

  // Uniformly scaled content must still REST (the motion caps scale with content,
  // so settling is scale-invariant — same tick-count, drift → 0) and descend E
  // monotonically. Reproduces the pre-cap-scaling residual drift (7.7 wu) that a
  // fixed cap left on a 17× step.
  it('a scaled step rests legally with monotone E (caps scale with content)', () => {
    const e = seedStep(0, 700)
    const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
    let prevE = totalEnergy(e), maxRise = 0, maxDrift = 0
    for (let i = 0; i < 100; i++) { settleStep(e); const cur = totalEnergy(e); maxRise = Math.max(maxRise, cur - prevE); prevE = cur }
    for (const [id, b] of e.bodies) maxDrift = Math.max(maxDrift, Math.hypot(b.pos.x - before.get(id)!.x, b.pos.y - before.get(id)!.y))
    expect(maxDrift, `scaled step drifted ${maxDrift.toFixed(2)} wu (cap scaling should make it rest)`).toBeLessThanOrEqual(1.5)
    expect(maxRise, `scaled step E rose ${maxRise.toFixed(4)} (un-gated mover?)`).toBeLessThanOrEqual(1e-3)
  })
})


describe('settleStep — deterministic incremental relaxation', () => {
  it('same diagram, same steps, identical layout (seedless determinism)', () => {
    const d = unary.diagram
    const boundary = unary.boundary
    const a = mkEngine(d, boundary)
    const b = mkEngine(d, boundary)
    for (let i = 0; i < 200; i++) {
      settleStep(a)
      settleStep(b)
    }
    for (const id of a.bodies.keys()) {
      expect(a.bodies.get(id)!.pos).toEqual(b.bodies.get(id)!.pos)
      expect(a.bodies.get(id)!.theta).toEqual(b.bodies.get(id)!.theta)
    }
  })
})

describe('settleStep — drag pin', () => {
  it('holds a pinned body at the cursor while neighbours relax legally around it', () => {
    const h = new DiagramBuilder()
    const a = h.ref(h.root, 'A', sentence)
    const b = h.ref(h.root, 'B', sentence)
    const c = h.ref(h.root, 'C', sentence)
    void b; void c
    const e = mkEngine(h.build(), [])
    const pinPos = { x: 40, y: 40 }
    for (let i = 0; i < 400; i++) {
      settleStep(e, new Set([a]))
      const pa = e.bodies.get(a)!
      pa.pos = { ...pinPos }
    }
    const pinned = e.bodies.get(a)!
    expect(pinned.pos).toEqual(pinPos) // held exactly at the cursor
    // neighbours relaxed AROUND it: no other body overlaps the pinned disc
    for (const other of e.bodies.values()) {
      if (other.id === a) continue
      const dist = Math.hypot(other.pos.x - pinPos.x, other.pos.y - pinPos.y)
      expect(dist).toBeGreaterThan(other.discR + pinned.discR - 1e-6)
    }
  })

  it('excludes the pinned body from the cohesion pull (drag feels direct)', () => {
    // A sits far from a tight B/C cluster: cohesion (linear in distance) dominates
    // repulsion (1/d²) at A, so exclusion visibly changes A's one-step motion.
    const build = () => {
      const h = new DiagramBuilder()
      const a = h.ref(h.root, 'A', sentence)
      const b = h.ref(h.root, 'B', sentence)
      const c = h.ref(h.root, 'C', sentence)
      const e = mkEngine(h.build(), [])
      e.bodies.get(a)!.pos = { x: 100, y: 0 }
      e.bodies.get(b)!.pos = { x: 0, y: 5 }
      e.bodies.get(c)!.pos = { x: 0, y: -5 }
      return { e, a }
    }
    const pinned = build()
    const free = build()
    settleStep(pinned.e, new Set([pinned.a]))
    settleStep(free.e, null)
    const moved = (r: ReturnType<typeof build>): number => {
      const p = r.e.bodies.get(r.a)!.pos
      return Math.hypot(p.x - 100, p.y - 0)
    }
    expect(moved(pinned)).toBeLessThan(moved(free))
  })
})

describe('settleStep — live-loop safety (bounded, non-diverging energy)', () => {
  it('per-frame relaxation with a pinned body stays finite and settles (movement decays over windows)', () => {
    // Mirror the shell frame loop: settleStep every frame with one body pinned
    // at a fixed cursor. A live loop must neither produce NaN/Infinity nor
    // oscillate/diverge — total per-window movement of the free bodies must
    // trend down, not up.
    const h = new DiagramBuilder()
    const a = h.ref(h.root, 'A', UNARY)
    const b = h.ref(h.root, 'B', UNARY)
    const c = h.ref(h.root, 'C', UNARY)
    h.wire(h.root, [
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: b, port: { kind: 'arg', index: 0 } },
    ])
    void c
    const e = mkEngine(h.build(), [])
    const pinPos = { x: 30, y: -20 }
    const free = [...e.bodies.keys()].filter((id) => id !== a)

    const windowMovement = (): number => {
      const before = new Map(free.map((id) => [id, { ...e.bodies.get(id)!.pos }]))
      for (let i = 0; i < 30; i++) {
        settleStep(e, new Set([a]))
        const pa = e.bodies.get(a)!
        pa.pos = { ...pinPos }
      }
      let total = 0
      for (const id of free) {
        const p = e.bodies.get(id)!.pos
        const q = before.get(id)!
        expect(Number.isFinite(p.x) && Number.isFinite(p.y), `body ${id} finite`).toBe(true)
        total += Math.hypot(p.x - q.x, p.y - q.y)
      }
      return total
    }

    const first = windowMovement()
    let last = first
    for (let w = 0; w < 8; w++) last = windowMovement()
    // energy is bounded and decaying: the late window moves far less than the first
    expect(last).toBeLessThan(first)
    expect(last).toBeLessThan(2) // effectively settled, no sustained oscillation
    // the pin held exactly, and no free body sits on top of it
    expect(e.bodies.get(a)!.pos).toEqual(pinPos)
    for (const id of free) {
      const p = e.bodies.get(id)!.pos
      expect(Math.hypot(p.x - pinPos.x, p.y - pinPos.y)).toBeGreaterThan(0)
    }
  })
})

describe('two floating nodes settle (no vibration limit cycle)', () => {
  it('two unconnected ref nodes on the sheet come to rest', () => {
    const h = new DiagramBuilder()
    h.ref(h.root, 'A', sentence)
    h.ref(h.root, 'B', sentence)
    const d = h.build()
    const e = mkEngine(d, [])
    // long free run: track recent movement; it must decay to (near) zero
    let recent = Infinity
    for (let w = 0; w < 40; w++) {
      const before = [...e.bodies.values()].map((b) => ({ ...b.pos }))
      for (let t = 0; t < 100; t++) settleStep(e)
      recent = 0
      const after = [...e.bodies.values()]
      after.forEach((b, i) => { recent += Math.hypot(b.pos.x - before[i]!.x, b.pos.y - before[i]!.y) })
    }
    // after 4000 ticks the pair must be essentially stationary per 100-tick
    // window. Bound RE-DERIVED from this model's measured equilibrium (USER test
    // policy): measured 0.0006 (2026-07-05) — the elastica engine rests these two
    // dead still, no residual vibration; pinned at 0.1 with generous margin (the
    // old chain suite's 0.5 was a looser inherited number).
    expect(recent).toBeLessThan(0.1)
    // and legally separated, not overlapping
    const [a, b] = [...e.bodies.values()]
    const dist = Math.hypot(a!.pos.x - b!.pos.x, a!.pos.y - b!.pos.y)
    expect(dist).toBeGreaterThan(a!.discR + b!.discR)
  })
})
