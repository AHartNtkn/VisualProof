import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { requiredPorts } from '../../src/kernel/diagram/diagram'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine, carryOver, worldAnchor, portNormal, pkey, DISC_R, frameSlots, FRAME_CORNER_W, type FrameBounds } from '../../src/view/engine'
import { emptyDiagram } from '../../src/app/edit'

const p = (s: string) => parseTerm(s)

const nat = () => {
  const b = buildFregeTheory().relations.nat!
  return { d: b.diagram, boundary: b.boundary }
}

describe('mkEngine', () => {
  it('creates exactly one body per diagram node', () => {
    const h = new DiagramBuilder()
    h.termNode(h.root, p('\\x. x'))
    h.ref(h.root, 'Nat', 1)
    const d = h.build()
    const e = mkEngine(d, [])
    const nodeBodies = [...e.bodies.values()].filter((b) => b.kind !== 'junction')
    expect(nodeBodies).toHaveLength(2)
    expect(new Set(nodeBodies.map((b) => b.id))).toEqual(new Set(Object.keys(d.nodes)))
  })

  it('ref discs use the single standard disc size (uniform-disc law)', () => {
    const h = new DiagramBuilder()
    h.ref(h.root, 'Nat', 1)
    h.ref(h.root, 'ReallyLongRelationName', 3)
    const d = h.build()
    const e = mkEngine(d, [])
    const refs = [...e.bodies.values()].filter((b) => b.kind === 'ref')
    expect(refs).toHaveLength(2)
    for (const r of refs) expect(r.discR).toBeCloseTo(DISC_R + 1.5, 10)
  })

  it('law 4: every ref/atom port is bound by exactly one chain (PLAN 21: chains own connectivity)', () => {
    const { d, boundary } = nat()
    const e = mkEngine(d, boundary)
    for (const [id, node] of Object.entries(d.nodes)) {
      if (node.kind === 'term') continue // term outputs may exit; law 4 is about refs/atoms
      for (const port of requiredPorts(d, node)) {
        let count = 0
        for (const ch of e.chains.values()) {
          count += ch.binds.filter((b) => b.body === id && b.key === pkey(port)).length
        }
        expect(count, `port ${id}|${pkey(port)}`).toBe(1)
      }
    }
  })

  it('worldAnchor rotates the local anchor about the body centre by theta', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('\\x. x'))
    const d = h.build()
    const e = mkEngine(d, [])
    const b = e.bodies.get(n)!
    b.pos = { x: 10, y: -3 }
    b.theta = 0
    const a0 = worldAnchor(b, 'out')
    b.theta = Math.PI / 2
    const a1 = worldAnchor(b, 'out')
    // rotating the frame by +90° maps a local (lx,ly) to (-ly, lx) around pos
    const lx = a0.x - 10, ly = a0.y - -3
    expect(a1.x).toBeCloseTo(10 - ly, 9)
    expect(a1.y).toBeCloseTo(-3 + lx, 9)
    // the port normal tracks theta too
    expect(portNormal(b, 'out', { x: 100, y: -3 })).toBeCloseTo(Math.atan2(0, 1) + Math.PI / 2, 9)
  })
})

describe('frameSlots — canonical boundary slots on the rounded-rect perimeter', () => {
  // A centred square frame, half-side 40, corner radius FRAME_CORNER_W. Slot 0
  // is the top-edge midpoint; slots read clockwise (canvas y-down).
  const fb: FrameBounds = { minX: -40, maxX: 40, minY: -40, maxY: 40, frameR: 40, center: { x: 0, y: 0 } }

  /** Signed distance to the frame's rounded rectangle (negative inside, 0 on it). */
  const sdf = (px: number, py: number): number => {
    const hw = 40 - FRAME_CORNER_W, hh = 40 - FRAME_CORNER_W
    const qx = Math.abs(px) - hw, qy = Math.abs(py) - hh
    return Math.hypot(Math.max(qx, 0), Math.max(qy, 0)) + Math.min(Math.max(qx, qy), 0) - FRAME_CORNER_W
  }

  it('slot 0 is the top-edge midpoint, pointing outward (up in y-down)', () => {
    const [s0] = frameSlots(fb, 1)
    expect(s0!.point.x).toBeCloseTo(0, 9)
    expect(s0!.point.y).toBeCloseTo(-40, 9)
    // outward normal = -pi/2 (screen-up); its unit vector is (0,-1)
    expect(Math.cos(s0!.normal)).toBeCloseTo(0, 9)
    expect(Math.sin(s0!.normal)).toBeCloseTo(-1, 9)
  })

  it('four slots land on the four edge midpoints, clockwise', () => {
    const s = frameSlots(fb, 4)
    expect(s).toHaveLength(4)
    // top, right, bottom, left — clockwise in canvas y-down
    const expected = [{ x: 0, y: -40 }, { x: 40, y: 0 }, { x: 0, y: 40 }, { x: -40, y: 0 }]
    for (let i = 0; i < 4; i++) {
      expect(s[i]!.point.x).toBeCloseTo(expected[i]!.x, 6)
      expect(s[i]!.point.y).toBeCloseTo(expected[i]!.y, 6)
    }
  })

  it('every slot lies exactly on the drawn rounded-rect perimeter, with an outward normal', () => {
    for (const n of [1, 2, 3, 5, 7, 12]) {
      const slots = frameSlots(fb, n)
      expect(slots).toHaveLength(n)
      for (const sl of slots) {
        // on the perimeter: SDF ~ 0
        expect(Math.abs(sdf(sl.point.x, sl.point.y)), `slot at (${sl.point.x.toFixed(2)},${sl.point.y.toFixed(2)})`).toBeLessThan(1e-6)
        // stated normal points strictly outward from the frame centre
        const outward = Math.cos(sl.normal) * sl.point.x + Math.sin(sl.normal) * sl.point.y
        expect(outward).toBeGreaterThan(0)
      }
    }
  })

  it('slots proceed monotonically clockwise (increasing polar angle from the top, y-down)', () => {
    const slots = frameSlots(fb, 8)
    // polar angle measured clockwise from screen-up; slot 0 at ~0, strictly increasing
    const clockwiseAngle = (x: number, y: number): number => {
      const a = Math.atan2(x, -y) // 0 at top, +pi/2 at right (x>0), grows clockwise
      return a < -1e-9 ? a + 2 * Math.PI : a
    }
    let prev = -1
    for (const sl of slots) {
      const a = clockwiseAngle(sl.point.x, sl.point.y)
      expect(a).toBeGreaterThan(prev)
      prev = a
    }
  })

  it('degenerate frames (corner radius collapses the straight edges) keep slots distinct, on-perimeter, outward', () => {
    // When hw or hh <= FRAME_CORNER_W the straight edges vanish (r = min(corner,
    // hw, hh)) and the perimeter becomes a stadium or full circle. Slot placement
    // is by ARC LENGTH regardless, so slots must stay distinct and ride the drawn
    // rounded rect even when n far exceeds the edge count and the frame is
    // off-origin — the property the arc-length parameterization guarantees but
    // the 40-square cases above never exercise.
    const frames: FrameBounds[] = [
      { minX: -6, maxX: 6, minY: -6, maxY: 6, frameR: 6, center: { x: 0, y: 0 } },      // tiny square → full circle
      { minX: 0, maxX: 4, minY: -14, maxY: 6, frameR: 10, center: { x: 2, y: -4 } },    // tall stadium, off-origin
      { minX: -3, maxX: 3, minY: -3, maxY: 3, frameR: 3, center: { x: 0, y: 0 } },      // sub-corner square
    ]
    for (const f of frames) {
      const hw = (f.maxX - f.minX) / 2, hh = (f.maxY - f.minY) / 2
      const r = Math.min(FRAME_CORNER_W, hw, hh)
      // SDF to THIS frame's rounded rect (corner radius r, centred at f.center).
      const sdfDeg = (px: number, py: number): number => {
        const qx = Math.abs(px - f.center.x) - (hw - r), qy = Math.abs(py - f.center.y) - (hh - r)
        return Math.hypot(Math.max(qx, 0), Math.max(qy, 0)) + Math.min(Math.max(qx, qy), 0) - r
      }
      for (const n of [5, 12, 20]) {
        const slots = frameSlots(f, n)
        expect(slots).toHaveLength(n)
        for (const sl of slots) {
          expect(Math.abs(sdfDeg(sl.point.x, sl.point.y)), `slot off perimeter at (${sl.point.x.toFixed(2)},${sl.point.y.toFixed(2)})`).toBeLessThan(1e-6)
          const outward = Math.cos(sl.normal) * (sl.point.x - f.center.x) + Math.sin(sl.normal) * (sl.point.y - f.center.y)
          expect(outward, 'normal points outward from centre').toBeGreaterThan(0)
        }
        let minD = Infinity
        for (let i = 0; i < slots.length; i++) for (let j = i + 1; j < slots.length; j++) {
          minD = Math.min(minD, Math.hypot(slots[i]!.point.x - slots[j]!.point.x, slots[i]!.point.y - slots[j]!.point.y))
        }
        expect(minD, `n=${n} distinct slots on frame hw=${hw} hh=${hh}`).toBeGreaterThan(0)
      }
    }
  })
})

describe('carryOver', () => {
  it('shared body ids inherit pos/vel/theta from the previous engine', () => {
    const { d, boundary } = nat()
    const prev = mkEngine(d, boundary)
    // perturb prev so the carried state is unmistakably NOT a fresh seed
    let t = 0
    for (const b of prev.bodies.values()) {
      b.pos = { x: 42 + t, y: -7 - t }
      b.vel = { x: 1 + t, y: 2 }
      b.theta = 0.5 + t
      t++
    }
    const next = mkEngine(d, boundary) // same diagram → identical id set
    carryOver(prev, next)
    expect(next.bodies.size).toBe(prev.bodies.size)
    for (const [id, nb] of next.bodies) {
      const pb = prev.bodies.get(id)!
      expect(nb.pos).toEqual(pb.pos)
      expect(nb.vel).toEqual(pb.vel)
      expect(nb.theta).toBe(pb.theta)
    }
  })

  it('bodies absent from the previous engine keep their deterministic seed (new ids do not crash)', () => {
    const { d, boundary } = nat()
    const empty = mkEngine(emptyDiagram(), []) // zero bodies → nothing to carry
    const next = mkEngine(d, boundary)
    const reference = mkEngine(d, boundary) // mkEngine is deterministic: identical seeds
    expect(() => carryOver(empty, next)).not.toThrow()
    for (const [id, nb] of next.bodies) {
      const rb = reference.bodies.get(id)!
      expect(nb.pos).toEqual(rb.pos)
      expect(nb.vel).toEqual(rb.vel)
      expect(nb.theta).toBe(rb.theta)
    }
  })
})
