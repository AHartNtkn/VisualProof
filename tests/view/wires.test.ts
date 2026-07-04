import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine, frameBounds, frameSlots } from '../../src/view/engine'
import { vec } from '../../src/view/vec'
import { settle, recomputeRegions } from '../../src/view/relax'
import { computeLegs, hobbyBezier, boundaryExits } from '../../src/view/wires'

const p = (s: string) => parseTerm(s)

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

describe('hobbyBezier — Metafont velocity control arms', () => {
  it('control points leave the endpoints along the given tangents, forward', () => {
    const ta = 0.4, tb = Math.PI - 0.3
    const path = hobbyBezier({ x: 0, y: 0 }, ta, { x: 20, y: 5 }, tb)
    // c1 - from must be a positive multiple of (cos ta, sin ta)
    const d1x = path.c1.x - path.from.x, d1y = path.c1.y - path.from.y
    const len1 = Math.hypot(d1x, d1y)
    expect(len1).toBeGreaterThan(0)
    expect(wrap(Math.atan2(d1y, d1x) - ta)).toBeCloseTo(0, 6)
    const d2x = path.c2.x - path.to.x, d2y = path.c2.y - path.to.y
    const len2 = Math.hypot(d2x, d2y)
    expect(len2).toBeGreaterThan(0)
    expect(wrap(Math.atan2(d2y, d2x) - tb)).toBeCloseTo(0, 6)
  })
})

describe('computeLegs — chains draw tangent-continuously (PLAN 21 form)', () => {
  it('a 3-endpoint wire settles a degree-3 tree point; degree-2 points draw C1', () => {
    // three nodes sharing one line of identity => a tree chain with a
    // free Plateau junction (junction BODIES are gone — the junction is
    // the chain's own degree-3 point)
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('x'))
    const b = h.termNode(h.root, p('x'))
    const c = h.termNode(h.root, p('x'))
    const w = h.wire(h.root, [
      { node: a, port: { kind: 'freeVar', name: 'x' } },
      { node: b, port: { kind: 'freeVar', name: 'x' } },
      { node: c, port: { kind: 'freeVar', name: 'x' } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
    const ch = e.chains.get(w)!
    const junctions = ch.pts.map((_, i) => i).filter((i) => ch.adj[i]!.length >= 3)
    expect(junctions.length, 'the tree has a junction point').toBeGreaterThanOrEqual(1)
    // tangent continuity at degree-2 interior points: the drawn tangents of
    // the two incident segments at the point are the SAME through-direction
    const legged = computeLegs(e).filter((g) => g.leg.wid === w)
    for (let v = 0; v < ch.pts.length; v++) {
      if (ch.adj[v]!.length !== 2) continue
      const tangentsAtV: number[] = []
      for (const g of legged) {
        // interior ends carry wire-local ids w:<wid>:<idx>
        if (g.leg.from.body === `w:${w}:${v}`) tangentsAtV.push(g.ta)
        if (g.leg.to.body === `w:${w}:${v}`) tangentsAtV.push(g.tb)
      }
      if (tangentsAtV.length === 2) {
        const diff = wrap(tangentsAtV[0]! - tangentsAtV[1]!)
        // same through-direction read from either side: 0 or pi
        expect(Math.min(Math.abs(diff), Math.abs(Math.abs(diff) - Math.PI))).toBeLessThan(1e-6)
      }
    }
  })
})


describe('boundary exits are continuous around frame corners', () => {
  // Regression for the original side-snap report. The exit now terminates at a
  // fixed perimeter slot (assigned by boundary order), so a single boundary
  // wire's exit sits at slot 0 and only drifts as the frame itself grows with
  // the layout — continuity is trivial, and the sweep guards that it stays so.
  it('sweeping a boundary node through a corner sector moves the exit smoothly', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('x'))
    const m = h.termNode(h.root, p('\\z. z'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const d = h.build()
    const e = mkEngine(d, [w])
    // park the second body at the center so the sheet circle stays put
    e.bodies.get(m)!.pos = vec(0, 0)
    const nb = e.bodies.get(n)!
    let prev: { x: number; y: number } | null = null
    let prevTick: number | null = null
    let maxStep = 0
    let maxTickStep = 0
    // sweep through the north-east corner sector in fine steps
    for (let i = 0; i <= 60; i++) {
      const a = Math.PI / 4 - Math.PI / 6 + (i / 60) * (Math.PI / 3)
      nb.pos = { x: Math.cos(a) * 25, y: Math.sin(a) * 25 }
      recomputeRegions(e)
      const ex = boundaryExits(e).find((x) => x.wid === w)!
      if (prev !== null) {
        maxStep = Math.max(maxStep, Math.hypot(ex.path.to.x - prev.x, ex.path.to.y - prev.y))
        let dth = Math.abs(ex.tick.angle - prevTick!)
        while (dth > Math.PI) dth = Math.abs(dth - 2 * Math.PI)
        maxTickStep = Math.max(maxTickStep, dth)
      }
      prev = { x: ex.path.to.x, y: ex.path.to.y }
      prevTick = ex.tick.angle
    }
    // node moves ~1.3 units per sweep step; a continuous exit moves the same
    // order — a side-snap teleports it tens of units in one step
    expect(maxStep, `max exit-point step ${maxStep.toFixed(2)}`).toBeLessThan(6)
    expect(maxTickStep, `max tick rotation step ${maxTickStep.toFixed(3)} rad`).toBeLessThan(0.3)
  })
})

describe('boundary exits are order-faithful: slot assignment never changes as bodies move', () => {
  // The boundary is ordered data; each wire owns a fixed perimeter slot (slot i
  // for boundary index i, clockwise from the pip). No matter where the bodies
  // are dragged, boundary wire i's exit terminates at slot i — exits cannot
  // slip past each other, so the drawing keeps carrying the boundary order.
  const thy = buildFregeTheory()
  const plusComm = thy.theorems.find((t) => t.name === 'plusComm')!

  it('a 3-boundary diagram: exit i sits at slot i for every layout in a wild sweep', () => {
    const { diagram, boundary } = plusComm.lhs
    expect(boundary.length).toBe(3)
    const e = mkEngine(diagram, boundary)
    settle(e, 1200)
    const nodeIds = [...e.bodies.keys()].filter((id) => e.bodies.get(id)!.kind !== 'junction' && e.bodies.get(id)!.kind !== 'anchor')

    // Six deliberately different layouts, including ones that would make a
    // radial/nearest-edge scheme reorder the exits (bodies pushed to a single
    // quadrant so their radials bunch on one frame side).
    const layouts: { x: number; y: number }[][] = [
      [{ x: -30, y: -30 }, { x: 30, y: -30 }, { x: 0, y: 30 }],
      [{ x: 40, y: 5 }, { x: 42, y: -3 }, { x: 38, y: 9 }], // all crammed east
      [{ x: -5, y: -40 }, { x: 3, y: -42 }, { x: -1, y: -38 }], // all crammed north
      [{ x: 20, y: 20 }, { x: -25, y: 5 }, { x: 5, y: -25 }],
      [{ x: -40, y: -40 }, { x: -38, y: -42 }, { x: -42, y: -39 }], // all crammed north-west
      [{ x: 12, y: -3 }, { x: -8, y: 14 }, { x: 2, y: -11 }],
    ]
    // The invariant across every layout: boundary index -> slot index is the
    // identity, checked against the freshly recomputed slots (the frame grows
    // and shrinks with the layout, so the absolute points move — the ASSIGNMENT
    // does not).
    for (const layout of layouts) {
      nodeIds.forEach((id, k) => { if (layout[k]) e.bodies.get(id)!.pos = layout[k]! })
      recomputeRegions(e)
      const fb = frameBounds(e)!
      const slots = frameSlots(fb, boundary.length)
      const exits = boundaryExits(e)
      expect(exits).toHaveLength(3)
      const byWid = new Map(exits.map((x) => [x.wid, x]))
      boundary.forEach((wid, i) => {
        const ex = byWid.get(wid)!
        expect(ex.path.to.x, `boundary ${i} (${wid}) x at slot ${i}`).toBeCloseTo(slots[i]!.point.x, 6)
        expect(ex.path.to.y, `boundary ${i} (${wid}) y at slot ${i}`).toBeCloseTo(slots[i]!.point.y, 6)
      })
    }
  })
})

describe('plusComm acid test: the crossing is visible in the boundary-order wiring', () => {
  // The user report: "there is no way to distinguish the left-hand side and the
  // right-hand side of plusComm." With canonical slots the two sides draw their
  // boundary wires at the SAME fixed perimeter positions but into DIFFERENT plus
  // ports — lhs is Plus(a,b,o), rhs is Plus(b,a,o) — so slot 0 and slot 1 swap
  // which argument of the plus disc they feed. That swap is the theorem, and it
  // is now visible: the slot->plus-arg correspondence differs between the sides.
  const thy = buildFregeTheory()
  const plusComm = thy.theorems.find((t) => t.name === 'plusComm')!

  /** For each boundary slot, the plus-node argument index its wire connects to. */
  const slotToPlusArg = (side: { diagram: typeof plusComm.lhs.diagram; boundary: readonly string[] }): number[] => {
    const plusId = Object.entries(side.diagram.nodes)
      .find(([, n]) => n.kind === 'ref' && n.defId === 'plus')![0]
    return side.boundary.map((wid) => {
      const ep = side.diagram.wires[wid]!.endpoints.find((e) => e.node === plusId)!
      if (ep.port.kind !== 'arg') throw new Error('expected an arg port on the plus disc')
      return ep.port.index
    })
  }

  it('lhs and rhs put their fixed slots into different plus ports (slots 0 and 1 cross)', () => {
    const lhsMap = slotToPlusArg(plusComm.lhs)
    const rhsMap = slotToPlusArg(plusComm.rhs)
    expect(plusComm.lhs.boundary.length).toBe(plusComm.rhs.boundary.length)
    // lhs: slot0->arg0, slot1->arg1, slot2->arg2 (uncrossed)
    expect(lhsMap).toEqual([0, 1, 2])
    // rhs: slot0->arg1, slot1->arg0, slot2->arg2 (a and b commuted)
    expect(rhsMap).toEqual([1, 0, 2])
    // the drawings genuinely differ — the crossing is not hidden
    expect(rhsMap).not.toEqual(lhsMap)
  })

  it('both sides draw their exits at the SAME canonical slots, so only the wiring differs', () => {
    const pos = (dwb: typeof plusComm.lhs) => {
      const e = mkEngine(dwb.diagram, dwb.boundary)
      settle(e, 1200)
      const fb = frameBounds(e)!
      return { points: frameSlots(fb, dwb.boundary.length).map((s) => s.point), center: fb.center }
    }
    const lhs = pos(plusComm.lhs), rhs = pos(plusComm.rhs)
    // slot geometry is a pure function of the frame + count, so both sides (3
    // boundary wires each) place slots in the same canonical clockwise sequence
    // around their own frame centre; the ONLY difference is which plus port each
    // slot wires into (asserted above). Angle measured clockwise from screen-up.
    const ang = (r: { points: { x: number; y: number }[]; center: { x: number; y: number } }) =>
      r.points.map((pt) => {
        const a = Math.atan2(pt.x - r.center.x, -(pt.y - r.center.y)) // 0 up, grows clockwise
        return a < -1e-9 ? a + 2 * Math.PI : a
      })
    const la = ang(lhs), ra = ang(rhs)
    // slot 0 at the top (angle ~0), slots increase clockwise on both sides
    expect(la[0]).toBeCloseTo(0, 6)
    expect(ra[0]).toBeCloseTo(0, 6)
    for (let i = 1; i < 3; i++) {
      expect(la[i]).toBeGreaterThan(la[i - 1]!)
      expect(ra[i]).toBeGreaterThan(ra[i - 1]!)
    }
  })
})
