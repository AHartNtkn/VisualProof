import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine, DISC_R, worldBindAnchor, carryOver, frameSlots } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, establishProofFrame, establishProofSlotShift } from '../../src/view/relax'

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

describe('proof-wide boundary identity', () => {
  const plusComm = buildFregeTheory().theorems.find((theorem) => theorem.name === 'plusComm')!

  it('carries the slot shift across a rewrite', () => {
    const before = mkEngine(plusComm.lhs.diagram, plusComm.lhs.boundary)
    before.frame = { center: { x: 0, y: 0 }, half: 50 }
    before.slotShift = 2
    const after = mkEngine(plusComm.rhs.diagram, plusComm.rhs.boundary)
    carryOver(before, after)
    expect(after.slotShift, 'carryOver carries the proof-wide slot-shift').toBe(2)
  })

  it('maps the commuted boundary slots to different plus ports', () => {
    const slotToPlusArg = (side: typeof plusComm.lhs): number[] => {
      const plusId = Object.entries(side.diagram.nodes)
        .find(([, node]) => node.kind === 'ref' && node.defId === 'plus')![0]
      return side.boundary.map((wire) => {
        const endpoint = side.diagram.wires[wire]!.endpoints.find((candidate) => candidate.node === plusId)!
        if (endpoint.port.kind !== 'arg') throw new Error('expected an arg port on the plus disc')
        return endpoint.port.index
      })
    }

    const lhsMap = slotToPlusArg(plusComm.lhs)
    const rhsMap = slotToPlusArg(plusComm.rhs)
    expect(lhsMap).toEqual([0, 1, 2])
    expect(rhsMap).toEqual([1, 0, 2])
    expect(rhsMap).not.toEqual(lhsMap)
  })

  it('chooses a legal slot shift that shortens the total boundary chord', () => {
    const steps = [{ diagram: plusComm.lhs.diagram, boundary: plusComm.lhs.boundary }]
    const probe = mkEngine(steps[0]!.diagram, steps[0]!.boundary)
    establishProofFrame(probe, steps)
    const frame = probe.frame!
    const shift = establishProofSlotShift(frame, steps)
    const count = steps[0]!.boundary.length
    const bounds = {
      minX: frame.center.x - frame.half,
      maxX: frame.center.x + frame.half,
      minY: frame.center.y - frame.half,
      maxY: frame.center.y + frame.half,
      frameR: frame.half,
      center: frame.center,
    }
    const slots = frameSlots(bounds, count)
    const totalChord = (candidateShift: number): number => {
      const engine = mkEngine(plusComm.lhs.diagram, plusComm.lhs.boundary)
      recomputeRegions(engine)
      resolveOverlaps(engine)
      let total = 0
      engine.boundary.forEach((wire, index) => {
        const bind = engine.wires.get(wire)?.binds[0]
        if (bind === undefined) return
        const port = worldBindAnchor(engine, engine.bodies.get(bind.body)!, bind.key)
        const slot = slots[(index + candidateShift) % count]!
        total += Math.hypot(slot.point.x - port.x, slot.point.y - port.y)
      })
      return total
    }

    expect(shift).toBeGreaterThanOrEqual(0)
    expect(shift).toBeLessThan(count)
    const chosen = totalChord(shift)
    for (let candidate = 0; candidate < count; candidate++) {
      expect(chosen).toBeLessThanOrEqual(totalChord(candidate) + 1e-6)
    }
    expect(chosen).toBeLessThan(totalChord(0))
  })
})
