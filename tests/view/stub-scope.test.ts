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

  it('∀-shape: a 2-endpoint wire scoped between the cuts grows a dangling ∃ branch THERE (never contorts)', () => {
    // ∀x (P(x) ∧ Q(x)) — the line's two endpoints sit inside the inner cut,
    // but the line is quantified in the annulus. USER rendering rule: the
    // line connects its ports naturally (junction at the dca) and a dangling
    // ∃ node homed at the scope carries the quantifier — the line itself
    // never detours through the annulus.
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
    const j = e.bodies.get(`j:${w}`)
    expect(j, 'the port connectivity keeps a junction near the ports').toBeDefined()
    expect(j!.region, 'junction homes at the dca — the line does not contort into the annulus').toBe(c2)
    const x = e.bodies.get(`x:${w}`)
    expect(x, 'the quantifier is a dangling ∃ body at the scope').toBeDefined()
    expect(x!.region).toBe(c1)
    expect(e.legs.filter((l) => l.wid === w).length).toBe(3)
    settle(e, 600)
    recomputeRegions(e)
    const g2 = e.regions.get(c2)!
    const dist = Math.hypot(x!.pos.x - g2.center.x, x!.pos.y - g2.center.y)
    expect(dist, 'the ∃ dot sits outside the inner cut').toBeGreaterThan(g2.radius)
    const stub = existentialStubs(e).find((s) => s.wid === w)
    expect(stub, 'the dangling branch end draws the ∃ dot').toBeDefined()
    expect(stub!.dot.x).toBe(x!.pos.x)
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
