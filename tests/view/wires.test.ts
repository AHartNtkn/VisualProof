import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { vec } from '../../src/view/vec'
import { settle, recomputeRegions } from '../../src/view/relax'
import { computeLegs, hobbyBezier, boundaryExits } from '../../src/view/wires'

const p = (s: string) => parseTerm(s)

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

describe('boundary exits are continuous around frame corners', () => {
  // Live feel report: the exit snapped between frame sides when its node
  // rounded a corner — the nearest-edge candidate scheme teleports the exit
  // point across the frame, and the per-side tick/tangent snaps 90°. The
  // exit is now the ray–rounded-rect intersection (continuous everywhere),
  // with the tick following the frame tangent.
  it('sweeping a boundary node through a corner sector moves the exit smoothly', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('x'))
    const m = h.termNode(h.root, p('\\z. z'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const d = h.build()
    const e = mkEngine(d, [w])
    // park the second body at the center so the sheet circle stays put
    e.bodies.get(m)!.pos = vec(0, 0)
    const nb = e.bodies.get(n)!
    let prev: { x: number; y: number } | null = null
    let prevTick: number | null = null
    let maxStep = 0
    let maxTickStep = 0
    // sweep through the north-east corner sector in fine steps
    for (let i = 0; i <= 60; i++) {
      const a = Math.PI / 4 - Math.PI / 6 + (i / 60) * (Math.PI / 3)
      nb.pos = { x: Math.cos(a) * 25, y: Math.sin(a) * 25 }
      recomputeRegions(e)
      const ex = boundaryExits(e).find((x) => x.wid === w)!
      if (prev !== null) {
        maxStep = Math.max(maxStep, Math.hypot(ex.path.to.x - prev.x, ex.path.to.y - prev.y))
        let dth = Math.abs(ex.tick.angle - prevTick!)
        while (dth > Math.PI) dth = Math.abs(dth - 2 * Math.PI)
        maxTickStep = Math.max(maxTickStep, dth)
      }
      prev = { x: ex.path.to.x, y: ex.path.to.y }
      prevTick = ex.tick.angle
    }
    // node moves ~1.3 units per sweep step; a continuous exit moves the same
    // order — a side-snap teleports it tens of units in one step
    expect(maxStep, `max exit-point step ${maxStep.toFixed(2)}`).toBeLessThan(6)
    expect(maxTickStep, `max tick rotation step ${maxTickStep.toFixed(3)} rad`).toBeLessThan(0.3)
  })
})
