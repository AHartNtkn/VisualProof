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

describe('law 7 (PLAN 21 form) — junction-kind bodies are exactly the homed wire ends', () => {
  for (const [name, d, boundary] of cases) {
    it(`junction bodies = chain homed points + bare wires in ${name}`, () => {
      const e = mkEngine(d, boundary)
      const homed = new Set<string>()
      for (const ch of e.chains.values()) for (const hm of ch.homed) homed.add(hm.bodyId)
      for (const [wid, w] of Object.entries(d.wires)) {
        if (w.endpoints.length === 0) homed.add(`j:${wid}`)
      }
      const junctions = [...e.bodies.values()].filter((b) => b.kind === 'junction')
      expect(new Set(junctions.map((b) => b.id))).toEqual(homed)
    })

    it(`every attached port is bound by exactly one chain in ${name}`, () => {
      const e = mkEngine(d, boundary)
      const perPort = new Map<string, number>()
      for (const ch of e.chains.values()) {
        for (const bind of ch.binds) {
          const k = `${bind.body}|${bind.key}`
          perPort.set(k, (perPort.get(k) ?? 0) + 1)
        }
      }
      for (const [port, count] of perPort) expect(count, port).toBe(1)
    })
  }
})

describe('settle — replay steps: bounded always; at rest unless topologically strained', () => {
  // Reproduces the runaway observed live at plusComm step 25 (22 bodies):
  // the settled "layout" was flying as a cluster at ~9 world units/tick with
  // its content spread across thousands of units. A legal settled layout must
  // ALWAYS stay anchored near the origin within the trivial packing bound
  // (every body inside a chain of discs at the rest gap).
  //
  // At-rest is asserted strictly where the layout truly rests. Steps whose
  // WIRING conflicts with their cut-NESTING (legs from deep content to hub
  // junctions want distances the region circles cannot give) settle into a
  // strained compromise that wanders slowly in a near-flat conflicted valley
  // (~0.05 u/tick, measured plateaus after 10k+ ticks under every field
  // variant tried — see plan 14's redesign record). Those get a REGRESSION
  // BOUND at ~2x the measured plateau: it pins the achieved behavior against
  // backsliding toward the historical 20–150 u runaways and documents the
  // open limitation; it does NOT claim rest.
  const r = mkReplay(plusCommThm, bootCtx)
  const restBound: Record<number, number> = { 32: 8, 48: 6 }
  for (const k of [0, 16, 32, 48, r.stepCount]) {
    it(`plusComm step ${k} settles bounded${restBound[k] !== undefined ? ' (strained: regression-bounded drift)' : ' and at rest'}`, () => {
      const e = mkEngine(r.diagramAt(k), r.boundary)
      settle(e, 2600)
      const discSum = [...e.bodies.values()].reduce((s, b) => s + 2 * b.discR + 20, 0)
      for (const b of e.bodies.values()) {
        const dist = Math.hypot(b.pos.x, b.pos.y)
        expect(dist, `body ${b.id} at distance ${dist.toFixed(0)} — content flew away (packing bound ${discSum.toFixed(0)})`).toBeLessThanOrEqual(discSum)
      }
      const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
      for (let i = 0; i < 50; i++) settleStep(e)
      const bound = restBound[k] ?? 1
      for (const [id, b] of e.bodies) {
        const p = before.get(id)!
        const moved = Math.hypot(b.pos.x - p.x, b.pos.y - p.y)
        expect(moved, `body ${id} moved ${moved.toFixed(2)} in 50 post-settle ticks (bound ${bound})`).toBeLessThanOrEqual(bound)
      }
    })
  }
})

describe('settle — observed jitter reproductions (live feel reports)', () => {
  // succShiftS@24 truly rests (slow convergence — bounded soft forces pace
  // the approach, hence the larger budget); plusComm@20 and succShiftS@48
  // carry the wiring-vs-nesting strain described above and get regression
  // bounds instead of rest claims.
  const succShiftS = bootCtx.theorems.get('succShiftS')!
  const jitterCases: [string, number, () => { d: Diagram; b: readonly WireId[] }, number][] = [
    ['plusComm@20', 2600, () => { const r2 = mkReplay(plusCommThm, bootCtx); return { d: r2.diagramAt(20), b: r2.boundary } }, 6],
    ['succShiftS@24', 7800, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(24), b: r2.boundary } }, 2],
    ['succShiftS@48', 2600, () => { const r2 = mkReplay(succShiftS, bootCtx); return { d: r2.diagramAt(48), b: r2.boundary } }, 12],
  ]
  for (const [name, budget, mk, bound] of jitterCases) {
    it(`${name} ${bound <= 2 ? 'rests' : 'is regression-bounded'} (<=${bound} over 200 post-settle ticks)`, () => {
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
    // after 4000 ticks the pair must be essentially stationary per 100-tick window
    expect(recent).toBeLessThan(0.5)
    // and legally separated, not overlapping
    const [a, b] = [...e.bodies.values()]
    const dist = Math.hypot(a!.pos.x - b!.pos.x, a!.pos.y - b!.pos.y)
    expect(dist).toBeGreaterThan(a!.discR + b!.discR)
  })
})
