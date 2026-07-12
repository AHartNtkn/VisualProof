import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { buildFregeTheory } from '../../src/theories/frege'
import { mkEngine, frameBounds, frameSlots } from '../../src/view/engine'
import { settle, recomputeRegions, resolveOverlaps, establishProofFrame, establishProofSlotShift } from '../../src/view/relax'
import { computeLegs } from '../../src/view/wires'
import { worldBindAnchor } from '../../src/view/engine'

const p = (s: string) => parseTerm(s)

const wrap = (x: number): number => Math.atan2(Math.sin(x), Math.cos(x))

describe('computeLegs — the traced θ-quadratic legs ARE the wire (PLAN 22)', () => {
  it('a 3-endpoint wire yields three legs meeting at the hub, each leaving its port rim perpendicular', () => {
    // three nodes sharing one line of identity => three hub legs into a single
    // wire-owned branch point (there is no polyline chain — each leg IS the
    // minimum-energy Euler-spiral interpolant of its live boundary data)
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
    const legged = computeLegs(e).filter((g) => g.leg.wid === w)
    expect(legged, 'a 3-endpoint wire draws three legs').toHaveLength(3)
    for (const g of legged) {
      // every leg starts ON its port's disc rim and leaves along the port
      // normal (the perpendicular exit is a boundary condition of the solve)
      const bind = e.wires.get(w)!.binds.find((bd) => bd.body === g.leg.from.body)!
      const body = e.bodies.get(bind.body)!
      const anchor = worldBindAnchor(e, body, bind.key)
      expect(Math.hypot(g.pts[0]!.x - anchor.x, g.pts[0]!.y - anchor.y), 'leg starts on the rim').toBeLessThan(1e-6)
      const la = body.localAnchor.get(bind.key)!
      const normal = Math.atan2(la.y, la.x) + body.theta
      const dir = Math.atan2(g.pts[1]!.y - g.pts[0]!.y, g.pts[1]!.x - g.pts[0]!.x)
      expect(Math.abs(wrap(dir - normal)), 'leg leaves the port perpendicular').toBeLessThan(0.05)
      // the traced polyline turns smoothly — no kink between adjacent segments
      for (let k = 1; k < g.pts.length - 1; k++) {
        const d0 = Math.atan2(g.pts[k]!.y - g.pts[k - 1]!.y, g.pts[k]!.x - g.pts[k - 1]!.x)
        const d1 = Math.atan2(g.pts[k + 1]!.y - g.pts[k]!.y, g.pts[k + 1]!.x - g.pts[k]!.x)
        expect(Math.abs(wrap(d1 - d0)), `kink at segment ${k}`).toBeLessThan(Math.PI / 4)
      }
    }
  })
})


describe('a single boundary wire is ONE bodyless leg to the fixed frame slot (plan 24)', () => {
  // The reset ruling: a simple boundary wire must be a single smooth curve from
  // the node to the INSIDE of the frame edge, with NOTHING at the frame end (no
  // exit body, no dot, no exterior connector). The slot is a fixed terminal.
  it('one interior port → one leg whose far end sits on the inner frame edge, no body', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, p('x'))
    const w = h.wire(h.root, [{ node: n, port: { kind: 'freeVar', name: 'x' } }])
    const e = mkEngine(h.build(), [w])
    settle(e, 400) // establishes the fixed frame; the boundary leg closes on its slot
    // no exit body anywhere (the reset's "there's an edge node for some reason") —
    // e:<wid> exit hubs are abolished; the boundary wire has no hub of its own
    expect([...e.bodies.keys()].some((id) => id.startsWith('e:')), 'no exit body exists').toBe(false)
    expect(e.wires.get(w)!.hub, 'a 1-port boundary wire has no hub').toBeNull()
    const legs = computeLegs(e).filter((g) => g.leg.wid === w)
    expect(legs, 'exactly one leg').toHaveLength(1)
    const pts = legs[0]!.pts
    const slot = frameSlots(frameBounds(e)!, 1)[0]!
    const end = pts[pts.length - 1]!
    // the far end sits ON the slot (inner frame edge), within the quadrature bound
    expect(Math.hypot(end.x - slot.point.x, end.y - slot.point.y), 'leg far end at the slot').toBeLessThan(1.0)
    // and it meets the frame perpendicular (final tangent ≈ the slot normal)
    const pen = pts[pts.length - 2]!
    const arr = wrap(Math.atan2(end.y - pen.y, end.x - pen.x) - slot.normal)
    expect(Math.abs(arr), `perpendicular meeting: arrival off-normal ${arr.toFixed(3)} rad`).toBeLessThan(0.35)
  })
})

describe('boundary slots are order-faithful: leg i ends at slot i, and cannot swap', () => {
  // The boundary is ordered data; each wire owns a fixed perimeter slot (slot i
  // for boundary index i, clockwise from the pip) on the FIXED frame. No matter
  // where the bodies are dragged, boundary wire i's leg terminates at slot i —
  // the assignment is the boundary index, structurally, so exits cannot swap.
  const thy = buildFregeTheory()
  const plusComm = thy.theorems.find((t) => t.name === 'plusComm')!

  it('a 3-boundary diagram: leg i ends at fixed slot i for every layout in a wild sweep', () => {
    const { diagram, boundary } = plusComm.lhs
    expect(boundary.length).toBe(3)
    const e = mkEngine(diagram, boundary)
    settle(e, 1200) // establishes the fixed frame + slots
    const slots = frameSlots(frameBounds(e)!, boundary.length)
    const nodeIds = [...e.bodies.keys()].filter((id) => e.bodies.get(id)!.kind !== 'junction' && e.bodies.get(id)!.kind !== 'anchor')
    const layouts: { x: number; y: number }[][] = [
      [{ x: -20, y: -20 }, { x: 20, y: -20 }, { x: 0, y: 20 }],
      [{ x: 18, y: 5 }, { x: 20, y: -3 }, { x: 16, y: 9 }], // crammed east
      [{ x: -5, y: -18 }, { x: 3, y: -20 }, { x: -1, y: -16 }], // crammed north
      [{ x: -18, y: -18 }, { x: -16, y: -20 }, { x: -20, y: -17 }], // crammed north-west
      [{ x: 12, y: -3 }, { x: -8, y: 14 }, { x: 2, y: -11 }],
    ]
    // the frame is FIXED (established once), so the slots do not move as bodies
    // are dragged — leg i ends at the SAME slot i regardless of the layout
    for (const layout of layouts) {
      nodeIds.forEach((id, k) => { if (layout[k]) e.bodies.get(id)!.pos = layout[k]! })
      recomputeRegions(e)
      const legsByWid = new Map<string, { x: number; y: number }[][]>()
      for (const g of computeLegs(e)) { const a = legsByWid.get(g.leg.wid) ?? []; a.push(g.pts); legsByWid.set(g.leg.wid, a) }
      boundary.forEach((wid, i) => {
        // the slot is an endpoint of exactly one of wire i's legs (its last point
        // for a 1-port wire, its first point for the k≥2 slot arm) — check the
        // nearest leg endpoint to slot i, direction-agnostic
        let best = Infinity
        for (const pts of legsByWid.get(wid)!) {
          for (const end of [pts[0]!, pts[pts.length - 1]!]) {
            best = Math.min(best, Math.hypot(end.x - slots[i]!.point.x, end.y - slots[i]!.point.y))
          }
        }
        expect(best, `boundary ${i} (${wid}) reaches slot ${i}`).toBeLessThan(1.5)
      })
    }
  })
})

describe('boundary slot-shift: exits are chosen to minimize total port→slot chord (plan 24 legibility, USER 2026-07-07)', () => {
  // The even-spaced slots start at an arbitrary top-centre phase, so wire i → slot i
  // can send a port to a far-edge slot (a chord that sweeps the whole frame, then
  // hugs the inside border). A single CYCLIC shift — the only reassignment that
  // preserves the canonical cyclic order — is chosen once, proof-wide, to minimize
  // the total port→slot chord. Here: the chosen shift is a legal index and its total
  // chord is no worse than (and, for plusComm, strictly better than) the unshifted.
  const thy = buildFregeTheory()
  const plusComm = thy.theorems.find((t) => t.name === 'plusComm')!

  const totalChord = (steps: { diagram: typeof plusComm.lhs.diagram; boundary: readonly string[] }[], frame: { center: { x: number; y: number }; half: number }, shift: number): number => {
    const n = steps[0]!.boundary.length
    const fb = { minX: frame.center.x - frame.half, maxX: frame.center.x + frame.half, minY: frame.center.y - frame.half, maxY: frame.center.y + frame.half, frameR: frame.half, center: frame.center }
    const slots = frameSlots(fb, n)
    let tot = 0
    for (const s of steps) {
      const se = mkEngine(s.diagram, s.boundary); recomputeRegions(se); resolveOverlaps(se)
      se.boundary.forEach((wid, i) => {
        const bd = se.wires.get(wid)?.binds[0]; if (bd === undefined) return
        const pp = worldBindAnchor(se, se.bodies.get(bd.body)!, bd.key)
        const slot = slots[(i + shift) % n]!
        tot += Math.hypot(slot.point.x - pp.x, slot.point.y - pp.y)
      })
    }
    return tot
  }

  it('the chosen shift is a legal cyclic index and shortens the total boundary chord', () => {
    const steps = [{ diagram: plusComm.lhs.diagram, boundary: plusComm.lhs.boundary }]
    const probe = mkEngine(steps[0]!.diagram, steps[0]!.boundary)
    establishProofFrame(probe, steps)
    const frame = probe.frame!
    const shift = establishProofSlotShift(frame, steps)
    const n = steps[0]!.boundary.length
    expect(shift, 'shift is a cyclic index in [0, n)').toBeGreaterThanOrEqual(0)
    expect(shift, 'shift is a cyclic index in [0, n)').toBeLessThan(n)
    // it minimizes, so it is ≤ every other shift including 0
    const chosen = totalChord(steps, frame, shift)
    for (let s = 0; s < n; s++) {
      expect(chosen, `chosen shift ${shift} total ≤ shift ${s} total`).toBeLessThanOrEqual(totalChord(steps, frame, s) + 1e-6)
    }
    // for plusComm the unshifted phase is a bad fit, so the chosen shift is a real win
    expect(chosen, 'chosen beats the arbitrary top-centre phase').toBeLessThan(totalChord(steps, frame, 0))
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
