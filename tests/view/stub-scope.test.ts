import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine, wireTerminalBCs, wireTerminalPoints, worldBindAnchor } from '../../src/view/engine'
import { UNARY } from '../fixtures/zero-signature'

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
    const n = b.ref(c2, 'Buried', UNARY)
    const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
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
    expect(wv.end, 'the ∃ tip is the root-homed loose body').toMatchObject({ body: `j:${w}` })
    expect(wv.binds).toHaveLength(1)
  })

  it('a same-region 2-endpoint wire stays a direct leg (no via body)', () => {
    const b = new DiagramBuilder()
    const pn = b.ref(b.root, 'P', UNARY)
    const qn = b.ref(b.root, 'Q', UNARY)
    const w = b.wire(b.root, [
      { node: pn, port: { kind: 'arg', index: 0 } },
      { node: qn, port: { kind: 'arg', index: 0 } },
    ])
    const e = mkEngine(b.build(), [])
    expect(e.bodies.get(`j:${w}`)).toBeUndefined()
    const wv = e.wires.get(w)!
    expect(wv.binds).toHaveLength(2)
    expect('end' in wv ? wv.end : null, 'a same-scope 2-ender is a direct port→port leg, no via body').toBeNull()
    expect(wv.net.edges).toHaveLength(1)
  })

  it('a same-region singleton carries its loose end as a circular body with identity scale', () => {
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'Unary', UNARY)
    const identity = b.identity(b.root, IOTA, 2)
    const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
    const d = b.build()
    const e = mkEngine(d, [])
    const loose = e.bodies.get(`j:${w}`)
    const identityBody = e.bodies.get(identity)!
    expect(loose).toBeDefined()
    expect(loose!.region).toBe(d.root)
    expect(loose!.geometry).not.toBeNull()
    expect(loose!.geometry!.arcs).toHaveLength(1)
    expect(loose!.geometry!.outerRadius).toBe(identityBody.geometry!.outerRadius)
    expect(loose!.discR).toBe(identityBody.discR)
    const wv = e.wires.get(w)!
    expect(wv.end).toMatchObject({ body: `j:${w}` })
  })

  it('clamps a rotated singleton end on its rim, then routes farther out on its radial normal', () => {
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'Unary', UNARY)
    const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
    const e = mkEngine(b.build(), [])
    const wire = e.wires.get(w)!
    const end = wire.end
    expect(end, 'the singleton endpoint is an explicit wire bind').toBeDefined()
    const body = e.bodies.get(end.body)!
    body.pos = { x: 21, y: -8 }
    body.theta = -Math.PI / 4
    e.scale = 1.75
    const terminalIndex = wire.binds.length + wire.slots.length
    const local = body.localAnchor.get(end.key)!
    const anchor = worldBindAnchor(e, body, end.key)
    const terminal = wireTerminalPoints(e, wire)[terminalIndex]!
    const bc = wireTerminalBCs(e, wire)[terminalIndex]
    const radial = Math.atan2(local.y, local.x) + body.theta

    expect(Math.hypot(local.x, local.y)).toBeCloseTo(body.geometry!.arcs[0]!.r, 9)
    expect(Math.hypot(anchor.x - body.pos.x, anchor.y - body.pos.y))
      .toBeCloseTo(Math.hypot(local.x, local.y) * e.scale, 9)
    expect(Math.hypot(anchor.x - body.pos.x, anchor.y - body.pos.y)).toBeGreaterThan(0)
    expect(Math.hypot(terminal.x - body.pos.x, terminal.y - body.pos.y))
      .toBeGreaterThan(Math.hypot(anchor.x - body.pos.x, anchor.y - body.pos.y))
    expect(bc).not.toBeNull()
    expect(bc!.p).toEqual(anchor)
    expect(bc!.n.x).toBeCloseTo(Math.cos(radial), 9)
    expect(bc!.n.y).toBeCloseTo(Math.sin(radial), 9)
  })
})

describe('zero-endpoint wires (a bare ∃) retain their scope-homed circular body', () => {
  it('mkEngine gives the bare existential a visible circular body', () => {
    // erasing a node can legally leave its wire with no endpoints: the bare
    // assertion that an individual exists — it must render, not crash
    const b = new DiagramBuilder()
    b.ref(b.root, 'Unary', UNARY)
    const w = b.wire(b.root, [])
    const d = b.build()
    const e = mkEngine(d, [])
    const body = e.bodies.get(`j:${w}`)
    expect(body, 'the bare ∃ is its own body at the wire scope').toBeDefined()
    expect(body!.region).toBe(d.root)
    expect(body!.geometry).not.toBeNull()
    expect(body!.geometry!.arcs).toHaveLength(1)
    expect(body!.geometry!.outerRadius).toBeGreaterThan(0)
  })
})
