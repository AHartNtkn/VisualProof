import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA } from '../../src/kernel/diagram/sig'
import { mkEngine, wireTerminalBCs, wireTerminalPoints, worldBindAnchor } from '../../src/view/engine'
import { bareWire } from '../fixtures/pins'
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
    const w = b.wire([{ node: n, port: { kind: 'arg', index: 0 } }])
    // the quantifier stays on the sheet though the port is two cuts deep: the
    // root pin is that outermost point of the line of identity
    const pin = b.pin(w, b.root)
    return { d: b.build(), n, w, pin, c1, c2 }
  }

  it('a root-scoped singleton wire on a buried node carries its loose end in a root-homed body', () => {
    const { d, w, pin } = build()
    const e = mkEngine(d, [])
    const loose = e.bodies.get(pin)
    expect(loose, 'the loose end needs its own body — the node body lives two cuts deep').toBeDefined()
    expect(loose!.region).toBe(d.root)
    const wv = e.wires.get(w)!
    expect(wv, 'the wire draws as a leg from the port out to the loose end').toBeDefined()
    expect(wv.binds[1], 'the ∃ tip is the root-homed loose body')
      .toEqual({ body: pin, key: 'i:0' })
    expect(wv.binds).toHaveLength(2)
  })

  it('a same-region 2-endpoint wire stays a direct leg (no via body)', () => {
    const b = new DiagramBuilder()
    const pn = b.ref(b.root, 'P', UNARY)
    const qn = b.ref(b.root, 'Q', UNARY)
    const w = b.wire([
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
    const identityRegion = b.cut(b.root)
    const identity = b.identity(identityRegion, IOTA, 2)
    const lhs = b.ref(b.root, 'Lhs', UNARY)
    const rhs = b.ref(b.root, 'Rhs', UNARY)
    b.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: lhs, port: { kind: 'arg', index: 0 } },
    ])
    b.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
      { node: rhs, port: { kind: 'arg', index: 0 } },
    ])
    const w = b.wire([{ node: n, port: { kind: 'arg', index: 0 } }])
    const d = b.build()
    const e = mkEngine(d, [])
    const wv = e.wires.get(w)!
    // build() completed the singleton with a pin at the port's own region
    const loosePin = wv.binds[1]!
    const loose = e.bodies.get(loosePin.body)
    const identityBody = e.bodies.get(identity)!
    expect(loose).toBeDefined()
    expect(loose!.region).toBe(d.root)
    expect(loose!.geometry).not.toBeNull()
    expect(loose!.geometry!.arcs).toHaveLength(1)
    expect(loose!.geometry!.outerRadius).toBe(identityBody.geometry!.outerRadius)
    expect(loose!.discR).toBe(identityBody.discR)
    expect(loosePin.key).toBe('i:0')
  })

  it('clamps a rotated singleton end on its rim, then routes farther out on its radial normal', () => {
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'Unary', UNARY)
    const w = b.wire([{ node: n, port: { kind: 'arg', index: 0 } }])
    const e = mkEngine(b.build(), [])
    const wire = e.wires.get(w)!
    const terminalIndex = 1 // terminals: the ref port, then the completing pin
    const end = wire.binds[terminalIndex]!
    expect(end, 'the singleton endpoint is an explicit wire bind').toBeDefined()
    const body = e.bodies.get(end.body)!
    body.pos = { x: 21, y: -8 }
    body.theta = -Math.PI / 4
    e.scale = 1.75
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
    const w = bareWire(b, b.root)
    const d = b.build()
    const e = mkEngine(d, [])
    const wv = e.wires.get(w)!
    // the bare ∃ is the segment between the two pins that hold its quantifier
    expect(wv.binds, 'a bare wire is held by exactly its two pins').toHaveLength(2)
    for (const bind of wv.binds) {
      const body = e.bodies.get(bind.body)
      expect(body, 'the bare ∃ draws as its own bodies at the wire scope').toBeDefined()
      expect(body!.region).toBe(d.root)
      expect(body!.geometry).not.toBeNull()
      expect(body!.geometry!.arcs).toHaveLength(1)
      expect(body!.geometry!.outerRadius).toBeGreaterThan(0)
    }
  })
})
