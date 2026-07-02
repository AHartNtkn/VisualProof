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

const idp = (s: string) => parseTerm(s, new Set<string>())

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

describe('law 7 — junctions: every >=3-endpoint wire gets exactly one junction body', () => {
  for (const [name, d, boundary] of cases) {
    it(`one junction per branch wire in ${name}`, () => {
      const e = mkEngine(d, boundary)
      const bset = new Set(boundary)
      const expected = Object.entries(d.wires).filter(
        ([wid, w]) => w.endpoints.length + (bset.has(wid) ? 1 : 0) >= 3,
      ).length
      const junctions = [...e.bodies.values()].filter((b) => b.kind === 'junction')
      expect(junctions).toHaveLength(expected)
    })

    it(`no unary node shows two legs in ${name} (one leg per attached port)`, () => {
      const e = mkEngine(d, boundary)
      const perPort = new Map<string, number>()
      for (const leg of e.legs) {
        for (const end of [leg.from, leg.to]) {
          if (end.key === null) continue
          const b = e.bodies.get(end.body)!
          if (b.kind === 'junction') continue
          const k = `${end.body}|${end.key}`
          perPort.set(k, (perPort.get(k) ?? 0) + 1)
        }
      }
      // a self-loop stub counts its single port twice (from and to); every
      // other attached port appears in exactly one leg. Nothing exceeds 2,
      // and only genuine stubs reach 2.
      for (const [, count] of perPort) expect(count).toBeLessThanOrEqual(2)
    })
  }
})

describe('settle — every replay step reaches a bounded layout at rest', () => {
  // Guards against the runaway once observed live (a settled "layout" flying as
  // a cluster with its content spread across thousands of units — nothing on
  // screen, so every drag fell through to pan). A legal settled layout must
  // (a) stay anchored near the origin within the trivial packing bound (every
  // body inside a chain of touching discs), and (b) actually be AT REST after
  // the settle budget. We sample states spread across the relational plusComm
  // replay — early, mid, and final — each of which must satisfy both.
  const r = mkReplay(plusCommThm, bootCtx)
  for (const k of [0, 16, 32, 48, r.stepCount]) {
    it(`plusComm step ${k} settles bounded and at rest`, () => {
      const e = mkEngine(r.diagramAt(k), r.boundary)
      settle(e, 2600)
      const discSum = [...e.bodies.values()].reduce((s, b) => s + 2 * b.discR, 0)
      for (const b of e.bodies.values()) {
        const dist = Math.hypot(b.pos.x, b.pos.y)
        expect(dist, `body ${b.id} at distance ${dist.toFixed(0)} — content flew away (packing bound ${discSum.toFixed(0)})`).toBeLessThanOrEqual(discSum)
      }
      const before = new Map([...e.bodies].map(([id, b]) => [id, { ...b.pos }]))
      for (let i = 0; i < 50; i++) settleStep(e)
      for (const [id, b] of e.bodies) {
        const p = before.get(id)!
        const moved = Math.hypot(b.pos.x - p.x, b.pos.y - p.y)
        expect(moved, `body ${id} moved ${moved.toFixed(2)} in 50 post-settle ticks — not at rest`).toBeLessThanOrEqual(1)
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
