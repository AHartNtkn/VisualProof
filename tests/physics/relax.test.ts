import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { carryOver, mkEngine, resolveLeg } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { settle, settleStep, totalEnergy, clampDragToFeasible, seedProject, establishProofFrame } from '../../src/view/relax'
import { thetaRange, legCache } from '../../src/view/elastica'
import { mkReplay } from '../../src/app/replay'
import { bootFixture } from '../app/boot-fixture'

const idp = (s: string) => parseTerm(s)

const bootCtx = (await bootFixture()).ctx
const plusCommThm = bootCtx.theorems.get('plusComm')!

const theory = buildFregeTheory()
const plusComm = theory.theorems.find((t) => t.name === 'plusComm')!
const succShiftS = theory.theorems.find((t) => t.name === 'succShiftS')!

const cases: [string, Diagram, readonly WireId[]][] = [
  ['plusComm.rhs', plusComm.rhs.diagram, plusComm.rhs.boundary],
  ['natBody', theory.relations.nat!.diagram, theory.relations.nat!.boundary],
  ['succShiftS.rhs', succShiftS.rhs.diagram, succShiftS.rhs.boundary],
]

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
function assertRestsLegalMonotone(name: string, e: Engine, driftBound: number): void {
  const discSum = [...e.bodies.values()].reduce((s, b) => s + 2 * b.discR + 20, 0)
  for (const b of e.bodies.values()) {
    const dist = Math.hypot(b.pos.x, b.pos.y)
    expect(dist, `${name}: body ${b.id} at ${dist.toFixed(0)} — content flew away (packing bound ${discSum.toFixed(0)})`).toBeLessThanOrEqual(discSum)
  }
  expect(anyOverlap(e), `${name}: region circles partially overlap at rest`).toBe(false)
  const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
  let prevE = totalEnergy(e), maxRise = 0
  for (let i = 0; i < 200; i++) { settleStep(e); const cur = totalEnergy(e); maxRise = Math.max(maxRise, cur - prevE); prevE = cur }
  for (const [id, b] of e.bodies) {
    const moved = Math.hypot(b.pos.x - before.get(id)!.x, b.pos.y - before.get(id)!.y)
    expect(moved, `${name}: body ${id} moved ${moved.toFixed(2)} over 200 post-settle ticks`).toBeLessThanOrEqual(driftBound)
  }
  expect(maxRise, `${name}: total E rose ${maxRise.toFixed(4)} in a post-settle tick (un-gated mover?)`).toBeLessThanOrEqual(1e-3)
}

describe('law 1 — containment: no two region circles ever intersect', () => {
  for (const [name, d, boundary] of cases) {
    it(`holds after settle for ${name}`, () => {
      const e = mkEngine(d, boundary)
      settle(e, 1100)
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
      for (let i = 0; i < 3; i++) h.termNode(cut, idp('\\x. x'))
    }
    const e = mkEngine(h.build(), [])
    settle(e, 1100)
    expect(anyOverlap(e), 'dense sibling cuts must not partially overlap').toBe(false)
  })
})

describe('law 7 (PLAN 22 form) — junction-kind bodies are exactly the wire-owned ends', () => {
  for (const [name, d, boundary] of cases) {
    it(`junction bodies = ∃ tips + ∀/boundary hub bodies + bare wires in ${name}`, () => {
      const e = mkEngine(d, boundary)
      // the wire-owned bodies: an ∃ tip, a hub BODY (a ∀ via-body or a boundary
      // exit hub), and a bare (0-endpoint) wire's lone dot
      const owned = new Set<string>()
      for (const w of e.wires.values()) {
        if (w.tipBodyId !== null) owned.add(w.tipBodyId)
        if (w.hub !== null && w.hub.kind === 'body') owned.add(w.hub.bodyId)
      }
      const boundaryWires = new Set(boundary)
      for (const [wid, w] of Object.entries(d.wires)) {
        // Endpointless boundary wires terminate at the fixed frame; only an
        // endpointless INTERNAL wire owns a bare existential-dot body.
        if (w.endpoints.length === 0 && !boundaryWires.has(wid)) owned.add(`j:${wid}`)
      }
      const junctions = [...e.bodies.values()].filter((b) => b.kind === 'junction')
      expect(new Set(junctions.map((b) => b.id))).toEqual(owned)
    })

    it(`every attached port is bound by exactly one wire leg in ${name}`, () => {
      const e = mkEngine(d, boundary)
      const perPort = new Map<string, number>()
      for (const w of e.wires.values()) {
        for (const bind of w.binds) {
          const k = `${bind.body}|${bind.key}`
          perPort.set(k, (perPort.get(k) ?? 0) + 1)
        }
      }
      for (const [port, count] of perPort) expect(count, port).toBe(1)
    })
  }
})

describe('settle — replay steps: content stays anchored, legal, rests, and E is monotone', () => {
  // Every replayed plusComm step must stay anchored (no runaway — reproduces the
  // historical step-25 cluster flying at ~9 u/tick), rest legally, and descend
  // total E monotonically at rest. plusComm@16 and @32 were plan-22 exit-hub LIMIT
  // CYCLES (documented it.fails, drift 55/15 over 200 ticks); the plan-23 strict-
  // total-energy-descent conversion (USER ruling) makes them genuine rests — the
  // it.fails are GONE. Budget RE-DERIVED from this model's measured time-to-rest
  // (USER policy): measured 2026-07-06, the slowest plusComm step rests by ~640
  // ticks; settled at 1100 with margin (was 7800 for the non-converging cycles).
  const r = mkReplay(plusCommThm, bootCtx)
  for (const k of [0, 16, 32, 48, r.actionCount]) {
    it(`plusComm step ${k} stays anchored, rests legally, E monotone`, () => {
      const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
      settle(e, 1100)
      assertRestsLegalMonotone(`plusComm@${k}`, e, 1.5)
    })
  }
})

describe('settle — observed jitter reproductions (live feel reports)', () => {
  // The user's original settling complaints, restated for the massless-elastica
  // model under strict total-energy descent. succShiftS@48 was a plan-22
  // documented it.fails (drifted 114.73 over 200 ticks — it RESTED before the
  // rotation DOF, which was a scene-dependent trade); the plan-23 conversion makes
  // it a genuine rest and the it.fails is GONE.
  const succShiftS = bootCtx.theorems.get('succShiftS')!
  // budget per fixture = measured time-to-rest + margin (2026-07-06): the uncapped
  // sibling barrier separates the connected cuts by cap-limited gated steps, so a
  // large diagram (succShiftS@48, 32 bodies) settles slower than the small ones.
  // [name, settle budget, drift bound, builder]. succShiftS@48 (32 bodies, the
  // largest scene) has a slower residual tail — its content descends monotonically
  // but a few nodes make ~1-wu discrete descents late; its drift bound is measured
  // (2026-07-06) at that larger settled value with margin, per USER test policy.
  const jitterCases: [string, number, number, () => { d: Diagram; b: readonly WireId[] }][] = [
    ['plusComm@20', 1100, 1.5, () => { const r2 = mkReplay(plusCommThm, bootCtx); return { d: r2.diagramAt(20), b: r2.boundaryAt(20) } }],
    // budget raised 1100→2500: folding the junction trunk terms into the node
    // gates (the strict-descent dual fix) is correct — E stays perfectly monotone
    // (0.00000 rise/tick) — but it lengthens this fixture's transient. MEASURED:
    // drift decays 4.49→0.52 over ticks 1100→2100 monotonically, resting under the
    // 1.5 bound by ~2100; pinned at 2500 with margin. The BOUND is unchanged — an
    // unconverged tail gets a longer budget, never a looser bound (plan-23 policy).
    ['succShiftS@24', 2500, 1.5, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(24), b: r2.boundaryAt(24) } }],
    ['succShiftS@48', 2500, 3, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(48), b: r2.boundaryAt(48) } }],
  ]
  for (const [name, budget, bound, mk] of jitterCases) {
    it(`${name} rests legally with monotone E over 200 post-settle ticks`, () => {
      const { d, b } = mk()
      const e = mkEngine(d, b)
      settle(e, budget)
      assertRestsLegalMonotone(name, e, bound)
    })
  }
})

describe('the leg-solve memo is output-neutral (plan 24 — exact cross-eval solve reuse)', () => {
  // The leg solve is a pure function of its boundary tuple; the sweep memoizes it in
  // a ring keyed on that exact tuple so a gate returning to its base after a rejected
  // trial reuses the base solve instead of recomputing it. Because a hit returns a
  // solution whose stored key EXACTLY equals the query, it equals a fresh solve, so
  // the memo cannot change any energy value, any accept/reject, or the settled layout.
  // Proof: settle the same fixture with the memo ON and OFF (legCache.enabled) and
  // require the two settled layouts to be BIT-IDENTICAL. Anything but 0 means the
  // reuse read a stale shape — the failure the explicit exact-key match forbids.
  function layoutSnapshot(e: Engine): number[] {
    const out: number[] = [e.slotShift]
    for (const b of e.bodies.values()) out.push(b.pos.x, b.pos.y, b.theta)
    for (const [, w] of e.wires) {
      out.push(w.phi)
      if (w.hub !== null && w.hub.kind === 'point') out.push(w.hub.pos.x, w.hub.pos.y)
      for (const leg of w.legs) out.push(leg.hubAngle)
    }
    return out
  }
  it('plusComm@20 settles BIT-IDENTICALLY with the leg-solve cache on vs off', () => {
    const build = (): Engine => { const r = mkReplay(plusCommThm, bootCtx); return mkEngine(r.diagramAt(20), r.boundaryAt(20)) }
    let on: number[], off: number[]
    try {
      legCache.enabled = true
      const eOn = build(); settle(eOn, 400); on = layoutSnapshot(eOn)
      legCache.enabled = false
      const eOff = build(); settle(eOff, 400); off = layoutSnapshot(eOff)
    } finally { legCache.enabled = true }
    expect(off.length).toBe(on.length)
    let maxDiff = 0
    for (let i = 0; i < on.length; i++) maxDiff = Math.max(maxDiff, Math.abs(on[i]! - off[i]!))
    expect(maxDiff, `the cache changed the settled layout by ${maxDiff} (must be exactly 0 — a pure memo)`).toBe(0)
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
      const e = mkEngine(diagram, boundary)
      settle(e, 800)
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
      const node = [...e.bodies.values()].find((b) => b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom')!
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
  const r = mkReplay(plusCommThm, bootCtx)
  const steps = Array.from({ length: r.actionCount + 1 }, (_, k) => ({ diagram: r.diagramAt(k), boundary: r.boundaryAt(k) }))
  // one fixed proof-wide frame, established once (as enterReplay does)
  const probe = mkEngine(r.diagramAt(0), r.boundaryAt(0))
  establishProofFrame(probe, steps)
  const frame = probe.frame!

  // build a step through the app seed path and settle it
  const seedStep = (k: number, ticks: number): Engine => {
    const e = mkEngine(r.diagramAt(k), r.boundaryAt(k))
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
  // occupancy 0.74–0.96 across plusComm steps; pinned ≥ 0.6 with margin. It also
  // must not spill past the border.
  for (const k of [0, r.actionCount]) {
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
    sparseBuilder.termNode(sparseBuilder.root, idp('x'))
    const sparse = mkEngine(sparseBuilder.build(), [])
    seedProject(sparse)
    const frameSnapshot = JSON.stringify(sparse.frame)
    const lifecycleFrame = sparse.frame!

    const denseBuilder = new DiagramBuilder()
    denseBuilder.termNode(denseBuilder.root, idp('x')) // n0 survives the rewrite
    for (let c = 0; c < 8; c++) {
      const cut = denseBuilder.cut(denseBuilder.root)
      for (let i = 0; i < 6; i++) denseBuilder.termNode(cut, idp('\\x. x'))
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
    const a = h.termNode(h.root, idp('x'))
    const b = h.termNode(h.root, idp('x'))
    const c = h.termNode(h.root, idp('x'))
    const wire = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
      { node: c, port: { kind: 'freeVar', name: 'x' } },
    ])
    const diagram = h.build()
    const first = mkEngine(diagram, [])
    seedProject(first)
    const firstBranch = { ...first.wires.get(wire)!.branches[0]! }
    expect(first.wires.get(wire)!.branches).toHaveLength(1)

    const rebuilt = mkEngine(diagram, [])
    carryOver(first, rebuilt)
    seedProject(rebuilt)
    const rebuiltBranch = rebuilt.wires.get(wire)!.branches[0]!

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

describe('free node rotation + local-only motion (plan 24, Subsystem 4)', () => {
  const wrapAng = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

  it('a single-port node ROTATES to face its wire (rotation reaches facing, no cap)', () => {
    // A node with one port can point that port at its wire's destination by
    // rotating — free rotation (no rate cap) reaches that facing at rest. (A
    // multi-port node cannot face all its ports at once; that is geometry, not a
    // rotation failure, so this law is scoped to single-port nodes.)
    for (const [name, diagram, boundary] of cases) {
      const e = mkEngine(diagram, boundary)
      settle(e, 800)
      for (const [, w] of e.wires) for (const leg of w.legs) {
        if (leg.a.kind !== 'bind') continue
        const b = e.bodies.get(w.binds[leg.a.i]!.body)!
        if (b.localAnchor.size > 1) continue // multi-port node: geometric compromise
        const sh = resolveLeg(e, w, leg)
        const toTarget = Math.atan2(sh.p1.y - sh.p0.y, sh.p1.x - sh.p0.x)
        const err = Math.abs(wrapAng(sh.th0 - toTarget)) * 180 / Math.PI
        expect(err, `${name}: single-port node ${b.id} faces ${err.toFixed(0)}° off its wire`).toBeLessThan(90)
      }
    }
  })

  it('no leg wraps the diagram: every settled leg has tangent range < π (blind cone unoccupied)', () => {
    // Free rotation keeps every port within a representable turn of its target, so
    // no leg falls into the >π blind cone that would draw a diagram-wrapping arc.
    for (const [name, diagram, boundary] of cases) {
      const e = mkEngine(diagram, boundary)
      settle(e, 800)
      for (const [, w] of e.wires) for (const leg of w.legs) {
        const sh = resolveLeg(e, w, leg)
        // the elastica enforces range ≤ π by construction; assert the resting
        // solution stays inside it (no >π blind-cone coil drawn at rest)
        const rng = Math.abs(thetaRange(sh.sol.c1, sh.sol.c2))
        expect(rng, `${name}: a settled leg tangent range ${(rng / Math.PI).toFixed(2)}π ≥ π (wrap)`).toBeLessThan(Math.PI)
      }
    }
  })

  it('motion is LOCAL: twisting one node does not move a distant non-wired node (no action at a distance)', () => {
    const e = mkEngine(cases[0]![1], cases[0]![2])
    settle(e, 800)
    const nodes = [...e.bodies.values()].filter((b) => b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom')
    const twisted = nodes[0]!
    // a node that shares no wire with `twisted` and is not touching it
    const wiredToTwisted = new Set<string>()
    for (const [, w] of e.wires) { const ids = w.binds.map((bd) => bd.body); if (ids.includes(twisted.id)) ids.forEach((i) => wiredToTwisted.add(i)) }
    const distant = nodes.find((b) => b.id !== twisted.id && !wiredToTwisted.has(b.id)
      && Math.hypot(b.pos.x - twisted.pos.x, b.pos.y - twisted.pos.y) > b.discR + twisted.discR + 10)
    if (distant !== undefined) {
      const before = { x: distant.pos.x, y: distant.pos.y }
      twisted.theta += 2.0 // a big twist
      settleStep(e)
      const moved = Math.hypot(distant.pos.x - before.x, distant.pos.y - before.y)
      expect(moved, `a distant non-wired node moved ${moved.toFixed(3)} when another was twisted`).toBeLessThan(0.6)
    }
  })

  it('node angular speed is UNBOUNDED: a mis-faced node turns more than the old 0.28 rad/tick cap in one tick', () => {
    // The node-rotation cap is gone (USER LAW: node angle is free). A node parked
    // far from its facing minimum crosses well past the old per-tick bound in a
    // single tick to shed wire tension — desired behaviour, not snapping.
    const [, diagram, boundary] = cases[0]!
    const e = mkEngine(diagram, boundary)
    settle(e, 800)
    const node = [...e.bodies.values()].find((b) => (b.kind === 'ref' || b.kind === 'term' || b.kind === 'atom') && [...e.wires.values()].some((w) => w.binds.some((bd) => bd.body === b.id)))!
    node.theta += 2.5 // knock it far from its faced rest orientation
    const before = node.theta
    settleStep(e)
    const turned = Math.abs(node.theta - before)
    expect(turned, `a mis-faced node turned only ${turned.toFixed(3)} rad — the cap is not gone`).toBeGreaterThan(0.28)
  })
})

describe('settleStep — deterministic incremental relaxation', () => {
  it('same diagram, same steps, identical layout (seedless determinism)', () => {
    const d = theory.relations.nat!.diagram
    const boundary = theory.relations.nat!.boundary
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
    const a = h.termNode(h.root, idp('\\x. x'))
    const b = h.termNode(h.root, idp('\\x. x'))
    const c = h.termNode(h.root, idp('\\x. x'))
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
      const a = h.termNode(h.root, idp('\\x. x'))
      const b = h.termNode(h.root, idp('\\x. x'))
      const c = h.termNode(h.root, idp('\\x. x'))
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
    const a = h.termNode(h.root, idp('\\x. x'))
    const b = h.termNode(h.root, idp('q'))
    const c = h.termNode(h.root, idp('\\f. \\x. f (f x)'))
    h.wire(h.root, [
      { node: a, port: { kind: 'output' } },
      { node: b, port: { kind: 'freeVar', name: 'q' } },
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

describe('two floating terms settle (no vibration limit cycle)', () => {
  it('two unconnected term nodes on the sheet come to rest', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, idp('\\x. x'))
    h.termNode(h.root, idp('\\x. \\y. x'))
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
