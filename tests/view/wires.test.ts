import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, IOTA } from '../../src/kernel/diagram/sig'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { UNARY } from '../fixtures/zero-signature'

/** An n-ary relation signature over individuals (ref/atom arity, new sig API). */
const rel = (n: number) => relSig(Array.from({ length: n }, () => IOTA))
import { mkEngine, DISC_R, worldBindAnchor, carryOver, frameSlots } from '../../src/view/engine'
import { recomputeRegions, resolveOverlaps, establishProofFrame, establishProofSlotShift } from '../../src/view/relax'

const commutedSides = (): {
  readonly lhs: DiagramWithBoundary
  readonly rhs: DiagramWithBoundary
} => {
  const side = (argumentAtBoundary: readonly number[]): DiagramWithBoundary => {
    const builder = new DiagramBuilder()
    const plus = builder.ref(builder.root, 'plus', rel(3))
    const boundary = argumentAtBoundary.map((index) =>
      builder.wire([
        { node: plus, port: { kind: 'arg', index } },
      ]))
    return { diagram: builder.build(), boundary }
  }
  return {
    lhs: side([1, 0, 2]),
    rhs: side([0, 1, 2]),
  }
}

describe('worldBindAnchor — wires attach to the DRAWN node rim, not the padded clearance disc (USER LAW: no floating attachments)', () => {
  it('a ref binds on its DISC_R rim, strictly inside the padded clearance disc', () => {
    const h = new DiagramBuilder()
    const r = h.ref(h.root, 'plus', rel(3))
    for (let i = 0; i < 3; i++) h.wire([{ node: r, port: { kind: 'arg', index: i } }])
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

  it('an atom bind reaches its rotated rim anchor; an identity bind stays centred', () => {
    const h = new DiagramBuilder()
    const cut = h.cut(h.root)
    const identity = h.identity(cut, IOTA, 2)
    const left = h.ref(h.root, 'Left', UNARY)
    const right = h.ref(h.root, 'Right', UNARY)
    h.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
      { node: left, port: { kind: 'arg', index: 0 } },
    ])
    h.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
      { node: right, port: { kind: 'arg', index: 0 } },
    ])
    const at = h.atom(h.root, rel(2))
    for (let i = 0; i < 2; i++) h.wire([{ node: at, port: { kind: 'arg', index: i } }])
    const e = mkEngine(h.build(), [])
    e.scale = 1.75
    const atomBody = e.bodies.get(at)!
    atomBody.theta = Math.PI / 3
    for (const [key, la] of atomBody.localAnchor) {
      const a = worldBindAnchor(e, atomBody, key)
      const c = Math.cos(atomBody.theta), s = Math.sin(atomBody.theta)
      const want = {
        x: atomBody.pos.x + e.scale * (la.x * c - la.y * s),
        y: atomBody.pos.y + e.scale * (la.x * s + la.y * c),
      }
      expect(Math.hypot(la.x, la.y), 'atom local bind anchor lies on its rim').toBeGreaterThan(0)
      expect(Math.hypot(a.x - want.x, a.y - want.y), 'atom wire starts at its drawn port anchor').toBeLessThan(1e-6)
      expect(Math.hypot(a.x - atomBody.pos.x, a.y - atomBody.pos.y), 'atom bind is not centered').toBeGreaterThan(0)
      expect(Math.hypot(a.x - atomBody.pos.x, a.y - atomBody.pos.y), 'and strictly inside the padded clearance disc (no float)').toBeLessThan(atomBody.discR * e.scale - 1e-6)
    }
    // the identity's drawn glyph IS its centre point, so its wires attach there
    const identityBody = e.bodies.get(identity)!
    identityBody.theta = Math.PI / 3
    for (const key of identityBody.localAnchor.keys()) {
      expect(worldBindAnchor(e, identityBody, key), 'identity wires attach at the drawn pip').toEqual(identityBody.pos)
    }
  })
})

describe('proof-wide boundary identity', () => {
  const commuted = commutedSides()

  it('carries the slot shift across a rewrite', () => {
    const before = mkEngine(commuted.lhs.diagram, commuted.lhs.boundary)
    before.frame = { center: { x: 0, y: 0 }, half: 50 }
    before.slotShift = 2
    const after = mkEngine(commuted.rhs.diagram, commuted.rhs.boundary)
    carryOver(before, after)
    expect(after.slotShift, 'carryOver carries the proof-wide slot-shift').toBe(2)
  })

  it('maps the commuted boundary slots to different plus ports', () => {
    const slotToPlusArg = (side: typeof commuted.lhs): number[] => {
      const plusId = Object.entries(side.diagram.nodes)
        .find(([, node]) => node.kind === 'ref' && node.defId === 'plus')![0]
      return side.boundary.map((wire) => {
        const endpoint = side.diagram.wires[wire]!.endpoints.find((candidate) => candidate.node === plusId)!
        if (endpoint.port.kind !== 'arg') throw new Error('expected an arg port on the plus disc')
        return endpoint.port.index
      })
    }

    const lhsMap = slotToPlusArg(commuted.lhs)
    const rhsMap = slotToPlusArg(commuted.rhs)
    expect(lhsMap).toEqual([1, 0, 2])
    expect(rhsMap).toEqual([0, 1, 2])
    expect(rhsMap).not.toEqual(lhsMap)
  })

  it('chooses a legal slot shift that shortens the total boundary chord', () => {
    const steps = [{ diagram: commuted.lhs.diagram, boundary: commuted.lhs.boundary }]
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
      const engine = mkEngine(commuted.lhs.diagram, commuted.lhs.boundary)
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
