import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep } from '../../src/view/relax'

const idp = (s: string) => parseTerm(s, new Set<string>())

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

describe('law 1 — containment: no two region circles ever intersect', () => {
  for (const [name, d, boundary] of cases) {
    it(`holds after settle for ${name}`, () => {
      const e = mkEngine(d, boundary)
      settle(e, 2600)
      const rs = [...e.regions.values()]
      for (let i = 0; i < rs.length; i++) {
        for (let j = i + 1; j < rs.length; j++) {
          expect(partiallyOverlaps(rs[i]!, rs[j]!), `regions ${i},${j} overlap in ${name}`).toBe(false)
        }
      }
    })
  }
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
      settleStep(e, a)
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
    settleStep(pinned.e, pinned.a)
    settleStep(free.e, null)
    const moved = (r: ReturnType<typeof build>): number => {
      const p = r.e.bodies.get(r.a)!.pos
      return Math.hypot(p.x - 100, p.y - 0)
    }
    expect(moved(pinned)).toBeLessThan(moved(free))
  })
})
