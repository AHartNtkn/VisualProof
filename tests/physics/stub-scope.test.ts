import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions } from '../../src/view/relax'
import { UNARY } from '../fixtures/zero-signature'

describe('existential stubs honor wire scope after settling', () => {
  const build = () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    const n = b.ref(c2, 'Buried', UNARY)
    const w = b.wire([{ node: n, port: { kind: 'arg', index: 0 } }])
    // the wire is quantified on the sheet even though its only port is two cuts
    // deep: the root pin is that quantifier point
    const pin = b.pin(w, b.root)
    return { d: b.build(), w, pin, c1 }
  }

  it('after settling, the ∃ dot sits OUTSIDE both cut circles (in its scope region)', () => {
    const { d, w, pin, c1 } = build()
    const e = mkEngine(d, [])
    settle(e, 600)
    recomputeRegions(e)
    const end = e.bodies.get(pin)
    expect(end, 'the loose end is the root-homed pin body').toBeDefined()
    expect(e.wires.get(w)!.binds.map((bind) => bind.body), 'the pin is a terminal of its wire')
      .toContain(pin)
    const g1 = e.regions.get(c1)!
    const dist = Math.hypot(end!.pos.x - g1.center.x, end!.pos.y - g1.center.y)
    expect(dist, 'the end body must not sit inside the outer cut — the individual is quantified on the sheet').toBeGreaterThan(g1.radius)
  })

  it('∀-shape: a 2-endpoint wire scoped between the cuts grows a dangling ∃ branch THERE (never contorts)', () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    const pn = b.ref(c2, 'P', UNARY)
    const qn = b.ref(c2, 'Q', UNARY)
    const w = b.wire([
      { node: pn, port: { kind: 'arg', index: 0 } },
      { node: qn, port: { kind: 'arg', index: 0 } },
    ])
    // both ports live in c2, so the quantifier only sits in the annulus if a pin
    // holds it there — the ∀ via, now a real node
    const via = b.pin(w, c1)
    const d = b.build()
    const e = mkEngine(d, [])
    const x = e.bodies.get(via)
    expect(x, 'the quantifier is a dangling ∃ body at the scope').toBeDefined()
    expect(x!.region).toBe(c1)
    const wv = e.wires.get(w)!
    expect(wv.binds).toHaveLength(3)
    expect(wv.binds[2], 'the ∀ via is the wire\'s third terminal — its pin node')
      .toEqual({ body: via, key: 'i:0' })
    // ruling A: the via is an ordinary free-end LEAF terminal of the Steiner tree over
    // {bind0, bind1, via} — a triple junction with the via as one tributary, not a star
    // hub. Two binds + one via = three terminals → exactly one branch vertex.
    expect(wv.net.junctions, 'a 2-bind ∀ + via starts as a 3-terminal star (one junction)').toHaveLength(1)
    const viaIdx = 2 // terminals: bind0, bind1, via pin
    expect(wv.net.edges.some(([u, v2]) => u === viaIdx || v2 === viaIdx), 'the via terminal is in the network').toBe(true)
    settle(e, 2600)
    recomputeRegions(e)
    const g2 = e.regions.get(c2)!
    const dist = Math.hypot(x!.pos.x - g2.center.x, x!.pos.y - g2.center.y)
    // resting exactly ON the ring IS outside — the scope barrier is one-sided,
    // so contact is a legal rest (float slack only)
    expect(dist, 'the ∃ dot sits outside the inner cut — the individual is quantified in the annulus').toBeGreaterThanOrEqual(g2.radius - 1e-6)
    expect(e.bodies.get(wv.binds[viaIdx]!.body), 'the dangling branch end is that same pin body')
      .toBe(x)
  })
})
