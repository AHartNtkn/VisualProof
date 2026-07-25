import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions } from '../../src/view/relax'
import { existentialStubs } from '../../src/view/wires'

const p = (s: string) => parseTerm(s)

describe('existential stubs honor wire scope after settling', () => {
  const build = () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    const n = b.termNode(c2, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    return { d: b.build(), w, c1 }
  }

  it('after settling, the ∃ dot sits OUTSIDE both cut circles (in its scope region)', () => {
    const { d, w, c1 } = build()
    const e = mkEngine(d, [])
    settle(e, 600)
    recomputeRegions(e)
    const stub = existentialStubs(e).find((s) => s.wid === w)
    expect(stub, 'the loose end still renders an ∃ dot').toBeDefined()
    const g1 = e.regions.get(c1)!
    const dist = Math.hypot(stub!.dot.x - g1.center.x, stub!.dot.y - g1.center.y)
    expect(dist, 'the dot must not sit inside the outer cut — the individual is quantified on the sheet').toBeGreaterThan(g1.radius)
  })

  it('∀-shape: a 2-endpoint wire scoped between the cuts grows a dangling ∃ branch THERE (never contorts)', () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    const pn = b.termNode(c2, p('p'))
    const qn = b.termNode(c2, p('q'))
    b.wire(c2, [{ node: pn, port: { kind: 'output' } }])
    b.wire(c2, [{ node: qn, port: { kind: 'output' } }])
    const w = b.wire(c1, [
      { node: pn, port: { kind: 'freeVar', name: 'p' } },
      { node: qn, port: { kind: 'freeVar', name: 'q' } },
    ])
    const d = b.build()
    const e = mkEngine(d, [])
    const x = e.bodies.get(`x:${w}`)
    expect(x, 'the quantifier is a dangling ∃ body at the scope').toBeDefined()
    expect(x!.region).toBe(c1)
    const wv = e.wires.get(w)!
    expect(wv.binds).toHaveLength(2)
    expect(wv.endBodyId, 'the ∀ via is the wire-owned end body').toBe(`x:${w}`)
    // ruling A: the via is an ordinary free-end LEAF terminal of the Steiner tree over
    // {bind0, bind1, via} — a triple junction with the via as one tributary, not a star
    // hub. Two binds + one via = three terminals → exactly one branch vertex.
    expect(wv.net.junctions, 'a 2-bind ∀ + via starts as a 3-terminal star (one junction)').toHaveLength(1)
    const viaIdx = 2 // terminals: bind0, bind1, end
    expect(wv.net.edges.some(([u, v2]) => u === viaIdx || v2 === viaIdx), 'the via terminal is in the network').toBe(true)
    settle(e, 2600)
    recomputeRegions(e)
    const g2 = e.regions.get(c2)!
    const dist = Math.hypot(x!.pos.x - g2.center.x, x!.pos.y - g2.center.y)
    // resting exactly ON the ring IS outside — the scope barrier is one-sided,
    // so contact is a legal rest (float slack only)
    expect(dist, 'the ∃ dot sits outside the inner cut — the individual is quantified in the annulus').toBeGreaterThanOrEqual(g2.radius - 1e-6)
    const stub = existentialStubs(e).find((s) => s.wid === w)
    expect(stub, 'the dangling branch end draws the ∃ dot').toBeDefined()
    expect(stub!.dot.x).toBe(x!.pos.x)
  })
})
