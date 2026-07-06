import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { settle, settleStep, totalEnergy, clampDragToFeasible } from '../../src/view/relax'
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
      for (const [wid, w] of Object.entries(d.wires)) {
        if (w.endpoints.length === 0) owned.add(`j:${wid}`)
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
  for (const k of [0, 16, 32, 48, r.stepCount]) {
    it(`plusComm step ${k} stays anchored, rests legally, E monotone`, () => {
      const e = mkEngine(r.diagramAt(k), r.boundary)
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
    ['plusComm@20', 1100, 1.5, () => { const r2 = mkReplay(plusCommThm, bootCtx); return { d: r2.diagramAt(20), b: r2.boundary } }],
    ['succShiftS@24', 1100, 1.5, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(24), b: r2.boundary } }],
    ['succShiftS@48', 2500, 3, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(48), b: r2.boundary } }],
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
