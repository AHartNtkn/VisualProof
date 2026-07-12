import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, DISC_R, worldBindAnchor } from '../../src/view/engine'

const p = (s: string) => parseTerm(s)

describe('worldBindAnchor — wires attach to the DRAWN node rim, not the padded clearance disc (USER LAW: no floating attachments)', () => {
  it('a ref binds on its DISC_R rim, strictly inside the padded clearance disc', () => {
    const h = new DiagramBuilder()
    const r = h.ref(h.root, 'plus', 3)
    for (let i = 0; i < 3; i++) h.wire(h.root, [{ node: r, port: { kind: 'arg', index: i } }])
    const e = mkEngine(h.build(), [])
    const b = e.bodies.get(r)!
    for (const key of b.localAnchor.keys()) {
      const a = worldBindAnchor(e, b, key)
      const d = Math.hypot(a.x - b.pos.x, a.y - b.pos.y)
      expect(d, 'ref wire starts on the DISC_R rim').toBeCloseTo(DISC_R, 6)
      expect(d, 'and strictly inside the padded clearance disc (no float)').toBeLessThan(b.discR - 1e-6)
    }
    e.scale = 2
    for (const key of b.localAnchor.keys()) {
      const a = worldBindAnchor(e, b, key)
      expect(Math.hypot(a.x - b.pos.x, a.y - b.pos.y), 'Engine.scale alone controls the live wire rim').toBeCloseTo(2 * DISC_R, 6)
    }
  })

  it('an atom/term binds on its port anchor (the drawn stub tip), strictly inside the padded clearance disc', () => {
    const h = new DiagramBuilder()
    const t = h.termNode(h.root, p('\\x. x y'))
    h.wire(h.root, [{ node: t, port: { kind: 'output' } }])
    h.wire(h.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }])
    const bub = h.bubble(h.root, 2)
    const at = h.atom(bub, bub)
    for (let i = 0; i < 2; i++) h.wire(bub, [{ node: at, port: { kind: 'arg', index: i } }])
    const e = mkEngine(h.build(), [])
    for (const id of [t, at]) {
      const b = e.bodies.get(id)!
      for (const [key, la] of b.localAnchor) {
        const a = worldBindAnchor(e, b, key)
        const c = Math.cos(b.theta), s = Math.sin(b.theta)
        const want = { x: b.pos.x + la.x * c - la.y * s, y: b.pos.y + la.x * s + la.y * c }
        expect(Math.hypot(a.x - want.x, a.y - want.y), `${b.kind} wire starts at its drawn port anchor`).toBeLessThan(1e-6)
        expect(Math.hypot(a.x - b.pos.x, a.y - b.pos.y), 'and strictly inside the padded clearance disc (no float)').toBeLessThan(b.discR - 1e-6)
      }
    }
  })
})
