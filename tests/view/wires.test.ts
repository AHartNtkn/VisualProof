import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle } from '../../src/view/relax'
import { computeLegs, hobbyBezier } from '../../src/view/wires'

const p = (s: string) => parseTerm(s, new Set<string>())

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

describe('hobbyBezier — Metafont velocity control arms', () => {
  it('control points leave the endpoints along the given tangents, forward', () => {
    const ta = 0.4, tb = Math.PI - 0.3
    const path = hobbyBezier({ x: 0, y: 0 }, ta, { x: 20, y: 5 }, tb)
    // c1 - from must be a positive multiple of (cos ta, sin ta)
    const d1x = path.c1.x - path.from.x, d1y = path.c1.y - path.from.y
    const len1 = Math.hypot(d1x, d1y)
    expect(len1).toBeGreaterThan(0)
    expect(wrap(Math.atan2(d1y, d1x) - ta)).toBeCloseTo(0, 6)
    const d2x = path.c2.x - path.to.x, d2y = path.c2.y - path.to.y
    const len2 = Math.hypot(d2x, d2y)
    expect(len2).toBeGreaterThan(0)
    expect(wrap(Math.atan2(d2y, d2x) - tb)).toBeCloseTo(0, 6)
  })
})

describe('computeLegs — junction trunk tangents flow tangent-continuously', () => {
  it('the two trunk tangents at a junction differ by pi', () => {
    // three nodes sharing one line of identity => a >=3-endpoint wire => junction
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('x'))
    const c = h.termNode(h.root, p('x'))
    h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
      { node: c, port: { kind: 'freeVar', name: 'x' } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 1200)
    const junctions = [...e.bodies.values()].filter((b) => b.kind === 'junction')
    expect(junctions.length).toBeGreaterThan(0)
    const legged = computeLegs(e)
    for (const j of junctions) {
      // the J-side tangent of each leg incident to this junction
      const tans: number[] = []
      for (const g of legged) {
        if (g.leg.from.body === j.id && g.leg.from.key === null) tans.push(g.ta)
        if (g.leg.to.body === j.id && g.leg.to.key === null) tans.push(g.tb)
      }
      expect(tans.length).toBeGreaterThanOrEqual(2)
      // some pair of incident tangents is exactly opposite (the chosen trunk)
      let foundOpposite = false
      for (let i = 0; i < tans.length; i++) {
        for (let k = i + 1; k < tans.length; k++) {
          if (Math.abs(Math.abs(wrap(tans[i]! - tans[k]!)) - Math.PI) < 1e-6) foundOpposite = true
        }
      }
      expect(foundOpposite, `junction ${j.id} has an opposite trunk pair`).toBe(true)
    }
  })
})
