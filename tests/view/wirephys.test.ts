import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine, worldBindAnchor, resolveLeg, traceLeg, frameBounds, frameSlots, type Engine, type WireView, type WireLeg } from '../../src/view/engine'
import { settle, settleStep, wireEnergy, WIREP } from '../../src/view/relax'
import { thetaRange, RANGE_B, QN, ELASTICA } from '../../src/view/elastica'
import { computeLegs, existentialStubs, boundaryExits } from '../../src/view/wires'

/**
 * PLAN 22 LAW BATTERY — wires as massless elastica in the ENGINE.
 * Every leg is the minimum-energy θ-quadratic interpolant of its live boundary
 * data (elastica.ts); the only wire DOF are the branch hub and the per-leg
 * arrival angles, descended with the bodies by one scalar energy (relax.ts).
 * These are the user's structural laws checked on the running engine — no chain,
 * no polyline state, no memory. Nothing here is a tuning artifact: a bound is a
 * documented equilibrium property or a measured regression guard, never a fudge.
 */

// ---- fixtures ----------------------------------------------------------

/** Three refs sharing a 3-way line (the k-adic showcase core). */
function threeWay(): { d: Diagram; b: WireId[] } {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'plus', 3)
  const r2 = b.ref(b.root, 'times', 3)
  const r3 = b.ref(b.root, 'succ', 2)
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
    { node: r3, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [] }
}

/** A dangling wire: one endpoint, free ∃ end homed at scope. */
function dangling(): { d: Diagram; b: WireId[]; node: string; wid: WireId } {
  const b = new DiagramBuilder()
  const n = b.ref(b.root, 'nat', 1)
  const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
  return { d: b.build(), b: [], node: n, wid: w }
}

/** The ∀ shape: 2-endpoint wire inside a cut, scoped at root — the dangle
    branch reaches a scope-homed via-body hub. */
function forallShape(): { d: Diagram; b: WireId[]; wid: WireId } {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const r1 = b.ref(cut, 'lt', 2)
  const r2 = b.ref(cut, 'gt', 2)
  const w = b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [], wid: w }
}

/** Crowded: a 2-ender forced to route past an interposed disc. */
function interposed(): { d: Diagram; b: WireId[] } {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'a', 1)
  const r2 = b.ref(b.root, 'b', 1)
  b.ref(b.root, 'wall', 1)
  b.termNode(b.root, parseTerm('\\x. x'))
  b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [] }
}

/** A boundary wire: one ref, one boundary endpoint reaching a frame slot. */
function boundaryOne(): { d: Diagram; b: WireId[]; wid: WireId } {
  const b = new DiagramBuilder()
  const n = b.ref(b.root, 'p', 1)
  b.termNode(b.root, parseTerm('\\x. x'))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
  return { d: b.build(), b: [w], wid: w }
}

const settled = (mk: () => { d: Diagram; b: WireId[] }, ticks = 8000): Engine => {
  const { d, b } = mk()
  const e = mkEngine(d, b)
  settle(e, ticks)
  return e
}

/** Every leg of a wire, resolved against the live state. */
function eachLeg(e: Engine, f: (w: WireView, leg: WireLeg) => void): void {
  for (const [, w] of e.wires) for (const leg of w.legs) f(w, leg)
}

// ---- structural impossibility (the engine's derived legs) ----------------

describe('wire physics — loops and kinks are unrepresentable at the engine level', () => {
  it('every leg in every settled fixture has tangent range < 2π (no self-crossing loop)', () => {
    for (const mk of [threeWay, dangling, forallShape, interposed, boundaryOne]) {
      const e = settled(mk)
      eachLeg(e, (w, leg) => {
        const s = resolveLeg(e, w, leg)
        // a monotone-curvature θ-quadratic self-crosses only past total turning
        // 2π; the solve's fallback caps at 2(π−ε) < 2π, so no drawn leg loops
        expect(thetaRange(s.sol.c1, s.sol.c2), `range at leg`).toBeLessThan(2 * Math.PI)
      })
    }
  })

  it('every leg is C¹: adjacent trace tangents differ by O(1/QN) (no kink)', () => {
    for (const mk of [threeWay, dangling, forallShape, interposed]) {
      const e = settled(mk)
      eachLeg(e, (w, leg) => {
        const s = resolveLeg(e, w, leg)
        const maxTurnPerStep = (Math.abs(s.sol.c1) + 2 * Math.abs(s.sol.c2)) / QN
        expect(maxTurnPerStep, `kink at a leg`).toBeLessThan(Math.PI / 4)
      })
    }
  })
})

// ---- memory (the solve is a pure function of the live boundary data) ------

describe('wire physics — zero wire memory (the purity law)', () => {
  it('an orbit-attack history leaves every leg identical to a fresh solve from the same state', () => {
    const e = settled(threeWay, 3000)
    // snapshot the exact rest state
    const rest = new Map([...e.bodies].map(([id, b]) => [id, { pos: { ...b.pos }, theta: b.theta }]))
    const hubs = [...e.wires].map(([wid, w]) => [wid, w.hub !== null && w.hub.kind === 'point' ? { ...w.hub.pos } : null] as const)
    const angles = [...e.wires].map(([wid, w]) => [wid, w.legs.map((l) => l.hubAngle)] as const)
    // fresh solve of every leg at rest (a fresh cache forces a real re-solve)
    const restSol = [...e.wires].flatMap(([, w]) => w.legs.map((leg) => {
      const s = resolveLeg(e, w, leg, { k: null, s: null })
      return { c1: s.sol.c1, c2: s.sol.c2, L: s.sol.L }
    }))
    // the orbit attack: drag every body through a wild circular sweep, mutating
    // every leg cache along the way
    for (let k = 0; k <= 40; k++) {
      const a = (k / 20) * Math.PI
      let i = 0
      for (const b of e.bodies.values()) { b.pos = { x: Math.cos(a + i) * 120, y: Math.sin(a + i) * 120 }; b.theta = a + i; i++ }
      for (const [, w] of e.wires) for (const leg of w.legs) resolveLeg(e, w, leg) // pollute caches
    }
    // restore the EXACT rest state
    for (const [id, b] of e.bodies) { const r = rest.get(id)!; b.pos = { ...r.pos }; b.theta = r.theta }
    for (const [wid, h] of hubs) { const w = e.wires.get(wid)!; if (h !== null && w.hub !== null && w.hub.kind === 'point') w.hub.pos = { ...h } }
    for (const [wid, as] of angles) { const w = e.wires.get(wid)!; w.legs.forEach((l, i) => { l.hubAngle = as[i]! }) }
    // re-solve through each leg's OWN (orbit-polluted) cache: a sound memoryless
    // memo must re-solve on the input mismatch and land bit-identical to the
    // fresh rest solve — history must leave NO trace
    const backSol = [...e.wires].flatMap(([, w]) => w.legs.map((leg) => {
      const s = resolveLeg(e, w, leg)
      return { c1: s.sol.c1, c2: s.sol.c2, L: s.sol.L }
    }))
    expect(backSol).toHaveLength(restSol.length)
    for (let i = 0; i < restSol.length; i++) {
      expect(Math.abs(backSol[i]!.c1 - restSol[i]!.c1), `leg ${i} c1 memory`).toBeLessThan(1e-9)
      expect(Math.abs(backSol[i]!.c2 - restSol[i]!.c2), `leg ${i} c2 memory`).toBeLessThan(1e-9)
      expect(Math.abs(backSol[i]!.L - restSol[i]!.L), `leg ${i} L memory`).toBeLessThan(1e-9)
    }
  })
})

// ---- rim closure under violent motion -------------------------------------

describe('wire physics — rim closure', () => {
  it('every representable leg closes on its target within the quadrature bound, even under violent body throws', () => {
    const { d, b } = interposed()
    const e = mkEngine(d, b)
    // throw the bodies to violent, far-flung positions (no settle — worst case)
    let i = 0
    for (const bd of e.bodies.values()) { bd.pos = { x: (i % 3) * 300 - 300, y: (i % 5) * 160 - 320 }; bd.theta = i * 1.3; i++ }
    eachLeg(e, (w, leg) => {
      const s = resolveLeg(e, w, leg)
      if (thetaRange(s.sol.c1, s.sol.c2) > RANGE_B + 1e-6) return // blind-cone marker: no closure by design
      const out: { x: number; y: number }[] = []
      traceLeg(s, out, 4 * QN)
      const end = out[out.length - 1]!
      expect(Math.hypot(end.x - s.p1.x, end.y - s.p1.y), `leg endpoint off its target`).toBeLessThan(0.75)
    })
  })
})

// ---- perpendicular exits (rim lock, by construction) ----------------------

describe('wire physics — perpendicular port exits at rest', () => {
  it('every leg starts ON its port rim and leaves along the port normal', () => {
    for (const mk of [threeWay, dangling, forallShape, interposed, boundaryOne]) {
      const e = settled(mk)
      for (const g of computeLegs(e)) {
        const w = e.wires.get(g.leg.wid)!
        const bind = w.binds.find((bd) => bd.body === g.leg.from.body && bd.key === g.leg.from.key)
        if (bind === undefined) continue // interior end
        const body = e.bodies.get(bind.body)!
        const anchor = worldBindAnchor(body, bind.key)
        expect(Math.hypot(g.pts[0]!.x - anchor.x, g.pts[0]!.y - anchor.y), 'starts on rim').toBeLessThan(1e-6)
        const la = body.localAnchor.get(bind.key)!
        const normal = Math.atan2(la.y, la.x) + body.theta
        const dir = Math.atan2(g.pts[1]!.y - g.pts[0]!.y, g.pts[1]!.x - g.pts[0]!.x)
        const dev = Math.atan2(Math.sin(dir - normal), Math.cos(dir - normal))
        expect(Math.abs(dev), `exit at ${bind.body}:${bind.key}`).toBeLessThanOrEqual(0.05)
      }
    }
  })
})

// ---- energy discipline (the master pins) ----------------------------------

describe('wire physics — energy discipline', () => {
  it('E is a bounded band under settleStep at rest: no spike, no creep (master pin)', () => {
    for (const mk of [threeWay, interposed, forallShape]) {
      const e = mkEngine(...mkArgs(mk))
      settle(e, 15000)
      const start = wireEnergy(e)
      let prev = start, maxTick = 0
      for (let i = 0; i < 120; i++) {
        settleStep(e)
        const cur = wireEnergy(e)
        maxTick = Math.max(maxTick, cur - prev)
        prev = cur
      }
      // the coupled explicit system delivers a BOUNDED band (see the integrator
      // note in relax.ts): single-tick rises stay small, and the net over the
      // window does not creep. Every real driver this model has rejected moved E
      // by many units per tick or walked it monotonically.
      expect(maxTick, `${mk.name}: max single-tick E rise ${maxTick.toFixed(3)}`).toBeLessThanOrEqual(1.6)
      expect(prev, `${mk.name}: net rise ${start.toFixed(2)} -> ${prev.toFixed(2)}`).toBeLessThanOrEqual(start + 0.5)
    }
  })

  it('bodies settle and STAY settled: no orbit, no conveyor (the user law)', () => {
    for (const mk of [threeWay, interposed, forallShape]) {
      const e = mkEngine(...mkArgs(mk))
      settle(e, 8000)
      const before = new Map([...e.bodies].map(([id, bb]) => [id, { ...bb.pos }]))
      for (let i = 0; i < 200; i++) settleStep(e)
      const drifts = [...e.bodies].map(([id, bb]) => ({ id, moved: Math.hypot(bb.pos.x - before.get(id)!.x, bb.pos.y - before.get(id)!.y) })).sort((a, b) => b.moved - a.moved)
      console.log(`no-orbit [${mk.name}]:`, drifts.slice(0, 3).map((x) => `${x.id}=${x.moved.toFixed(3)}`).join(' '))
      for (const { id, moved } of drifts) {
        // Bound RE-DERIVED from THIS model's measured equilibria (USER test
        // policy — never inherit the old chain suite's numbers): measured max
        // post-settle drift 2026-07-05 was threeWay 0.24 / interposed 0.04 /
        // forallShape 0.06 (16000-tick settle); pinned at 1.0 with margin. An
        // orbit or conveyor moves bodies by tens — this discriminates cleanly.
        expect(moved, `body ${id} drifted ${moved.toFixed(3)} over 200 post-settle ticks`).toBeLessThanOrEqual(1.0)
      }
    }
  })
})

// ---- equilibria ----------------------------------------------------------

describe('wire physics — equilibria', () => {
  it('the ∃ dot never rests sunk into its own wire (standoff law)', () => {
    const { d, b, wid } = dangling()
    const e = mkEngine(d, b)
    settle(e, 8000)
    const w = e.wires.get(wid)!
    const tip = e.bodies.get(w.tipBodyId!)!
    const bd = w.binds[0]!
    const anchor = worldBindAnchor(e.bodies.get(bd.body)!, bd.key)
    const dist = Math.hypot(tip.pos.x - anchor.x, tip.pos.y - anchor.y)
    // the standoff C1 ramp (radius standoffR) balances the single-tension pull
    // strictly inside the radius only under external compression; a free dangle
    // rests at or beyond it
    expect(dist, 'dot sunk into its wire').toBeGreaterThanOrEqual(WIREP.standoffR * 0.75)
  })

  it('a dangling ∃ end FOLLOWS its wire when the node moves (the dangle-tow law)', () => {
    const { d, b, node, wid } = dangling()
    const e = mkEngine(d, b)
    settle(e, 2600)
    const body = e.bodies.get(node)!
    const tip = e.bodies.get(e.wires.get(wid)!.tipBodyId!)!
    // the law is the REST SHAPE: after a disturbance the wire re-establishes its
    // relative geometry — BOTH ends participate (Newton's third law by
    // construction), so we assert the rest length is restored and the tip moved
    const relBefore = { x: tip.pos.x - body.pos.x, y: tip.pos.y - body.pos.y }
    const gapBefore = Math.hypot(relBefore.x, relBefore.y)
    body.pos = { x: body.pos.x + 40, y: body.pos.y }
    const tipAtDisturb = { ...tip.pos }
    settle(e, 2600)
    const gapAfter = Math.hypot(tip.pos.x - body.pos.x, tip.pos.y - body.pos.y)
    expect(Math.abs(gapAfter - gapBefore), 'the wire must restore its rest length').toBeLessThanOrEqual(gapBefore * 0.5)
    const moved = Math.hypot(tip.pos.x - tipAtDisturb.x, tip.pos.y - tipAtDisturb.y)
    expect(moved, 'the free end must move (not parked)').toBeGreaterThanOrEqual(5)
  })

  it('a free-space 3-way junction spreads its arrival directions toward 120° (Plateau)', () => {
    // three refs far apart around one hub, no interposed discs: the hub's three
    // hub-leg arrival directions relax toward mutual 120° (finite spread energy,
    // so the elastica bend torque can shift each by a bounded margin)
    const e = settled(threeWay, 12000)
    const w = [...e.wires.values()].find((x) => x.hub !== null)!
    const hub = w.hub!
    const hubPos = hub.kind === 'point' ? hub.pos : e.bodies.get(hub.bodyId)!.pos
    // the drawn arrival direction of each hub leg = the tangent of its traced
    // polyline as it reaches the hub
    const dirs: number[] = []
    for (const leg of w.legs) {
      if (leg.b.kind !== 'hub') continue
      const s = resolveLeg(e, w, leg)
      const pts: { x: number; y: number }[] = []
      traceLeg(s, pts, QN)
      const a = pts[pts.length - 1]!, prev = pts[pts.length - 2]!
      dirs.push(Math.atan2(a.y - prev.y, a.x - prev.x))
    }
    expect(dirs).toHaveLength(3)
    void hubPos
    // the three sorted arrival directions have cyclic gaps ~120° each, within a
    // bounded elastica-bend margin (finite spread energy shifts the soap-film
    // Plateau angle)
    const sorted = [...dirs].sort((x, y) => x - y)
    for (let k = 0; k < 3; k++) {
      const gap = (sorted[(k + 1) % 3]! - sorted[k]! + (k === 2 ? 2 * Math.PI : 0))
      expect(Math.abs(gap - (2 * Math.PI) / 3), `spread gap ${k} = ${(gap * 180 / Math.PI).toFixed(0)}°`).toBeLessThanOrEqual((35 * Math.PI) / 180)
    }
  })
})

// ---- boundary wires (merged hub + exit) -----------------------------------

describe('wire physics — boundary exits (the slot-attracted hub)', () => {
  it('a boundary wire routes its ports through a slot-attracted junction body (no exit point, no hub→exit leg)', () => {
    const { d, b, wid } = boundaryOne()
    const e = mkEngine(d, b)
    settle(e, 400) // boundaryExits needs the frame (region circles) populated
    const w = e.wires.get(wid)!
    expect(w.slot, 'the boundary wire owns a fixed frame slot').not.toBeNull()
    expect(w.hub, 'its ports meet at a hub body').not.toBeNull()
    const hub = w.hub!
    expect(hub.kind).toBe('body')
    expect(hub.kind === 'body' ? e.bodies.get(hub.bodyId)!.id : null).toBe(`e:${wid}`)
    expect(w.legs.every((l) => l.b.kind === 'hub'), 'every boundary leg arrives at the hub').toBe(true)
    // the exit hub is NOT drawn as a dangling ∃ dot — it rides the frame
    expect(existentialStubs(e).some((s) => s.wid === wid), 'boundary exit is not an ∃ dot').toBe(false)
    // it IS drawn as a frame exit connector to its slot
    expect(boundaryExits(e).some((x) => x.wid === wid), 'boundary wire draws a frame exit').toBe(true)
  })

  it('boundary slot assignment is canonical by boundary order and never reorders under a wild body sweep', () => {
    const { diagram, boundary } = threeBoundary()
    const e = mkEngine(diagram, boundary)
    settle(e, 1200)
    const layouts: { x: number; y: number }[][] = [
      [{ x: -30, y: -30 }, { x: 30, y: -30 }, { x: 0, y: 30 }],
      [{ x: 40, y: 5 }, { x: 42, y: -3 }, { x: 38, y: 9 }],
      [{ x: -5, y: -40 }, { x: 3, y: -42 }, { x: -1, y: -38 }],
    ]
    const nodeIds = [...e.bodies.keys()].filter((id) => { const k = e.bodies.get(id)!.kind; return k !== 'junction' && k !== 'anchor' })
    for (const layout of layouts) {
      nodeIds.forEach((id, k) => { if (layout[k]) e.bodies.get(id)!.pos = layout[k]! })
      // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
      const fb = frameBounds(e)!
      const slots = frameSlots(fb, boundary.length)
      const exits = boundaryExits(e)
      const byWid = new Map(exits.map((x) => [x.wid, x]))
      boundary.forEach((wid, i) => {
        const ex = byWid.get(wid)!
        const slotPt = ex.pts[ex.pts.length - 1]!
        expect(slotPt.x, `boundary ${i} at slot ${i} x`).toBeCloseTo(slots[i]!.point.x, 6)
        expect(slotPt.y, `boundary ${i} at slot ${i} y`).toBeCloseTo(slots[i]!.point.y, 6)
      })
    }
  })
})

// ---- regression bounds from the measured theorem scenes -------------------

import { mkReplay } from '../../src/app/replay'
import { bootFixture } from '../app/boot-fixture'
const bootCtx = (await bootFixture()).ctx
const threeBoundary = (): { diagram: Diagram; boundary: readonly WireId[] } => {
  const r = mkReplay(bootCtx.theorems.get('plusComm')!, bootCtx)
  return { diagram: r.diagramAt(0), boundary: r.boundary }
}
function mkArgs(mk: () => { d: Diagram; b: WireId[] }): [Diagram, WireId[]] {
  const { d, b } = mk()
  return [d, b]
}

void ELASTICA
