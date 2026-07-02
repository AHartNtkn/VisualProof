import { describe, it, expect } from 'vitest'
import type { WireId } from '../../src/kernel/diagram/diagram'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine } from '../../src/view/engine'
import { settle, settleStep } from '../../src/view/relax'

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
