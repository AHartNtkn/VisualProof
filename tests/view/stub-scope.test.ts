import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
import { settle, recomputeRegions } from '../../src/view/relax'
import { existentialStubs } from '../../src/view/wires'

const p = (s: string) => parseTerm(s)

/**
 * The ∃ dot marks WHERE the individual is quantified — the wire's SCOPE
 * region. A singleton wire scoped ABOVE its node's region (double-cut intro
 * deliberately keeps selected wires at their old scope: ∃x·¬¬φ ≡ ∃x·φ) must
 * dangle its loose end in the scope region, not hang off the node's port
 * inside the cuts as if it were quantified there.
 */
describe('existential stubs honor wire scope', () => {
  const build = () => {
    const b = new DiagramBuilder()
    const c1 = b.cut(b.root)
    const c2 = b.cut(c1)
    const n = b.termNode(c2, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }]) // scoped at ROOT
    return { d: b.build(), n, w, c1, c2 }
  }

  it('a root-scoped singleton wire on a buried node carries its loose end in a root-homed body', () => {
    const { d, w } = build()
    const e = mkEngine(d, [])
    const loose = e.bodies.get(`j:${w}`)
    expect(loose, 'the loose end needs its own body (junction of degree 1) — the node body lives two cuts deep').toBeDefined()
    expect(loose!.region).toBe(d.root)
    const leg = e.legs.find((l) => l.wid === w)
    expect(leg, 'the wire draws as a leg from the port out to the loose end').toBeDefined()
    expect(leg!.from.body === `j:${w}` || leg!.to.body === `j:${w}`).toBe(true)
    expect(leg!.from.body === leg!.to.body).toBe(false)
  })

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

  it('∀-shape: a 2-endpoint wire scoped between the cuts bulges its outermost point THERE (via body)', () => {
    // ∀x (P(x) ∧ Q(x)) — the line's two endpoints sit inside the inner cut,
    // but the line is quantified in the annulus: its outermost point must
    // visibly live between the cuts, not render as a direct connection.
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
    ]) // scoped at c1 — the annulus — while both endpoints live in c2
    const d = b.build()
    const e = mkEngine(d, [])
    const via = e.bodies.get(`j:${w}`)
    expect(via, 'the quantifier location needs its own body in the scope region').toBeDefined()
    expect(via!.region).toBe(c1)
    expect(e.legs.filter((l) => l.wid === w).length).toBe(2)
    settle(e, 600)
    recomputeRegions(e)
    const g2 = e.regions.get(c2)!
    const dist = Math.hypot(via!.pos.x - g2.center.x, via!.pos.y - g2.center.y)
    expect(dist, 'the outermost point of the line sits outside the inner cut').toBeGreaterThan(g2.radius)
  })

  it('a same-region 2-endpoint wire stays a direct leg (no via body)', () => {
    const b = new DiagramBuilder()
    const pn = b.termNode(b.root, p('p'))
    const qn = b.termNode(b.root, p('q'))
    b.wire(b.root, [{ node: pn, port: { kind: 'output' } }])
    b.wire(b.root, [{ node: qn, port: { kind: 'output' } }])
    const w = b.wire(b.root, [
      { node: pn, port: { kind: 'freeVar', name: 'p' } },
      { node: qn, port: { kind: 'freeVar', name: 'q' } },
    ])
    const e = mkEngine(b.build(), [])
    expect(e.bodies.get(`j:${w}`)).toBeUndefined()
    expect(e.legs.filter((l) => l.wid === w).length).toBe(1)
  })

  it('a same-region singleton ALSO carries its loose end as its own body (USER LAW: dangling ends are nodes)', () => {
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const d = b.build()
    const e = mkEngine(d, [])
    const loose = e.bodies.get(`j:${w}`)
    expect(loose).toBeDefined()
    expect(loose!.region).toBe(d.root)
    const leg = e.legs.find((l) => l.wid === w)!
    expect(leg.from.body === leg.to.body).toBe(false)
  })
})
