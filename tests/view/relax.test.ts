import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep } from '../../src/view/relax'
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

describe('law 1 — containment: no two region circles ever intersect', () => {
  for (const [name, d, boundary] of cases) {
    it(`holds after settle for ${name}`, () => {
      const e = mkEngine(d, boundary)
      settle(e, 2600)
      expect(anyOverlap(e), `regions overlap in ${name}`).toBe(false)
    })
  }

  // The bundled theorem sides are sparse enough that soft repulsion alone keeps
  // their region circles legal, so they do NOT exercise the hard overlap
  // projection. This dense case DOES: many sibling cuts are pulled together by
  // cohesion until, at the soft-force equilibrium, their circles partially
  // overlap — only resolveOverlaps (the projection in settleStep/settle) makes
  // the drawing legal. Removing that projection makes THIS assertion fail, which
  // is what pins law 1 to its mechanism.
  it('holds for a dense sheet of sibling cuts (requires overlap projection)', () => {
    const h = new DiagramBuilder()
    for (let c = 0; c < 10; c++) {
      const cut = h.cut(h.root)
      for (let i = 0; i < 3; i++) h.termNode(cut, idp('\\x. x'))
    }
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
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

describe('settle — replay steps: content stays anchored, and rests where the model can', () => {
  // A legal settled layout must ALWAYS stay anchored near the origin within the
  // trivial packing bound (every body inside a chain of discs at the rest gap) —
  // reproduces the historical plusComm step-25 runaway (a cluster flying at ~9
  // u/tick). And it must REST (settle-and-stay, USER law), bound RE-DERIVED from
  // this model's measured drift (USER test policy — never inherit old numbers):
  // measured 2026-07-05 (full-grid gate, settle 7800, 50 post-settle ticks):
  //   plusComm@0 0.03, @48 0.40, @64(=stepCount) 0.05 → rest, pinned at 2.
  //
  // KNOWN-BROKEN FIXTURES (it.fails — the FIXTURE does not rest, the TEST is
  // correct to demand it): plusComm@16 (50-tick drift 4.24, 200-tick 55.47) and
  // @32 (drift50 3.83, 200 15.38) are exit-hub LIMIT CYCLES — E swings ~1500 as
  // the exit hubs oscillate where one global content rotation cannot face all
  // three ports at their slots. Root cause is the non-gated content momentum
  // integrator + overlap projection re-exciting the gated wire descent; the fix
  // is the strict-total-energy-descent conversion (USER ruling 2026-07-05),
  // scoped as PLAN 23. it.fails keeps the suite honest AND green, and flips to a
  // real failure the day plan 23 makes these rest (prompting removal of it.fails).
  const r = mkReplay(plusCommThm, bootCtx)
  const brokenFixture = new Set([16, 32]) // exit-hub limit cycle — plan 23
  for (const k of [0, 16, 32, 48, r.stepCount]) {
    const runner = brokenFixture.has(k) ? it.fails : it
    runner(`plusComm step ${k} stays anchored and rests${brokenFixture.has(k) ? ' [KNOWN-BROKEN FIXTURE: exit-hub limit cycle → plan 23]' : ''}`, () => {
      const e = mkEngine(r.diagramAt(k), r.boundary)
      settle(e, 7800)
      const discSum = [...e.bodies.values()].reduce((s, b) => s + 2 * b.discR + 20, 0)
      for (const b of e.bodies.values()) {
        const dist = Math.hypot(b.pos.x, b.pos.y)
        expect(dist, `body ${b.id} at distance ${dist.toFixed(0)} — content flew away (packing bound ${discSum.toFixed(0)})`).toBeLessThanOrEqual(discSum)
      }
      const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
      for (let i = 0; i < 50; i++) settleStep(e)
      for (const [id, b] of e.bodies) {
        const p = before.get(id)!
        const moved = Math.hypot(b.pos.x - p.x, b.pos.y - p.y)
        expect(moved, `body ${id} moved ${moved.toFixed(2)} in 50 post-settle ticks`).toBeLessThanOrEqual(2)
      }
    })
  }
})

describe('settle — observed jitter reproductions (live feel reports)', () => {
  // The user's original settling complaints, restated for the massless-elastica
  // model. Bounds RE-DERIVED from this model's measured drift over 200 post-settle
  // ticks (USER test policy — never inherit the old chain suite's numbers):
  //   measured 2026-07-05 (full-grid gate, settle 7800):
  //   plusComm@20 0.44, succShiftS@24 0.65 → rest, pinned at 1.5.
  // The gated global-rotation DOF turns each boundary port toward its slot,
  // dissolving the blind-cone coils that used to flap these diagrams.
  //
  // KNOWN-BROKEN FIXTURE (it.fails — the FIXTURE does not rest, the TEST is right
  // to demand it): succShiftS@48 drifts 114.73 over 200 ticks (it RESTED at 4.58
  // BEFORE the rotation DOF — the DOF is a scene-dependent trade). Same exit-hub
  // limit cycle as plusComm@16/@32: a non-gated content integrator + projection
  // re-exciting the gated wire descent. Fix = strict-total-energy-descent
  // conversion (USER ruling 2026-07-05), scoped as PLAN 23; it.fails flips to a
  // real failure the day plan 23 makes it rest.
  const succShiftS = bootCtx.theorems.get('succShiftS')!
  const jitterCases: [string, number, () => { d: Diagram; b: readonly WireId[] }, number, boolean][] = [
    ['plusComm@20', 7800, () => { const r2 = mkReplay(plusCommThm, bootCtx); return { d: r2.diagramAt(20), b: r2.boundary } }, 1.5, false],
    ['succShiftS@24', 7800, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(24), b: r2.boundary } }, 1.5, false],
    ['succShiftS@48', 7800, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(48), b: r2.boundary } }, 2, true],
  ]
  for (const [name, budget, mk, bound, broken] of jitterCases) {
    const runner = broken ? it.fails : it
    runner(`${name} rests (<=${bound} over 200 post-settle ticks)${broken ? ' [KNOWN-BROKEN FIXTURE: exit-hub limit cycle → plan 23]' : ''}`, () => {
      const { d, b } = mk()
      const e = mkEngine(d, b)
      settle(e, budget)
      const before = new Map([...e.bodies].map(([id, bb]) => [id, { ...bb.pos }]))
      for (let i = 0; i < 200; i++) settleStep(e)
      for (const [id, bb] of e.bodies) {
        const p = before.get(id)!
        const moved = Math.hypot(bb.pos.x - p.x, bb.pos.y - p.y)
        expect(moved, `body ${id} moved ${moved.toFixed(2)} over 200 post-settle ticks`).toBeLessThanOrEqual(bound)
      }
    })
  }
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
      pa.vel = { x: 0, y: 0 }
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
        pa.vel = { x: 0, y: 0 }
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
