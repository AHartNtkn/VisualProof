import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine } from '../../src/view/engine'
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
    const wv = e.wires.get(w)!
    expect(wv, 'the wire draws as a leg from the port out to the loose end').toBeDefined()
    expect(wv.tipBodyId, 'the ∃ tip is the root-homed loose body').toBe(`j:${w}`)
    expect(wv.binds).toHaveLength(1)
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
    const wv = e.wires.get(w)!
    expect(wv.binds).toHaveLength(2)
    expect(wv.hub, 'a same-scope 2-ender is a direct port→port leg, no hub').toBeNull()
    expect(wv.tipBodyId).toBeNull()
    expect(wv.legs).toHaveLength(1)
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
    const wv = e.wires.get(w)!
    expect(wv.tipBodyId).toBe(`j:${w}`)
  })
})

describe('zero-endpoint wires (a bare ∃) render as a lone dot', () => {
  it('mkEngine gives the wire a scope-homed body and the dot renders', () => {
    // erasing a node can legally leave its wire with no endpoints: the bare
    // assertion that an individual exists — it must render, not crash
    const b = new DiagramBuilder()
    const n = b.termNode(b.root, p('\\x. x'))
    b.wire(b.root, [{ node: n, port: { kind: 'output' } }])
    const w = b.wire(b.root, [])
    const d = b.build()
    const e = mkEngine(d, [])
    const body = e.bodies.get(`j:${w}`)
    expect(body, 'the bare ∃ is its own body at the wire scope').toBeDefined()
    expect(body!.region).toBe(d.root)
    const stub = existentialStubs(e).find((s) => s.wid === w)
    expect(stub, 'the bare ∃ draws its dot').toBeDefined()
    expect(stub!.dot.x).toBe(body!.pos.x)
  })
})
