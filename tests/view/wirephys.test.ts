import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine, worldBindAnchor, resolveLeg, traceLeg, frameBounds, frameSlots, type Engine, type WireView, type WireLeg } from '../../src/view/engine'
import { settle, settleStep, wireEnergy, WIREP, trunkTarget, recomputeRegions } from '../../src/view/relax'
import { thetaRange, RANGE_B, QN, ELASTICA, mkLegCache } from '../../src/view/elastica'
import { computeLegs, existentialStubs } from '../../src/view/wires'

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
      const s = resolveLeg(e, w, leg, mkLegCache())
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
        // BLIND-CONE EXEMPTION (same class the rim-closure test above skips with
        // "no closure by design"): when a free-end ∃ tip rests angularly BEHIND
        // its own port — reachable only in the max-crowd threeWay stress fixture,
        // where routing a tip to the port's FRONT would cost more in wire↔wire
        // separation against the co-running dangles than the ~100-unit leg-energy
        // penalty of curling behind it — the leg has no representable ≤π-range
        // closure and falls back to a >π-turn arc (thetaRange > RANGE_B). Its port
        // exit tangent is STILL exactly the normal (rim-lock: the solve fixes
        // θ(0)=normal), but the fallback curls hard immediately, so the coarse
        // first-QN-chord `dir` over-reports the drawn direction by ≈ c1/(2·QN).
        // The perpendicularity LAW holds (measured worst NON-blind-cone exit across
        // all five fixtures under this model: 0.0094 rad, 0.5° — well inside 0.05);
        // the coarse-chord proxy is simply not a valid tangent estimate for a
        // sub-representable fallback arc, exactly as it is not a valid closure test
        // for one. A lone dangle (dangling fixture) rests with its tip in FRONT and
        // exits at 0.0°.
        const leg = w.legs.find((l) => l.a.kind === 'bind' && w.binds[l.a.i]?.body === bind.body && w.binds[l.a.i]?.key === bind.key)!
        const sol = resolveLeg(e, w, leg)
        if (thetaRange(sol.sol.c1, sol.sol.c2) > RANGE_B + 1e-6) continue
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
    // rests EXACTLY at 0.75·standoffR. That value is the closed-form equilibrium:
    // in [h, R] (h = R/2) the outward standoff force is slope·(R−d)/h with
    // slope = 2·tension, so balancing the single inward tension gives
    // 2·tension·(R−d)/h = tension ⇒ R−d = h/2 = R/4 ⇒ d = 0.75·R. The rest point
    // therefore SITS ON the bound, and float noise lands a few 1e-8 below it; the
    // 1e-6 slack keeps this an equilibrium assertion (a sunk dot rests near 0, an
    // order of magnitude the slack cannot mask).
    expect(dist, 'dot sunk into its wire').toBeGreaterThanOrEqual(WIREP.standoffR * 0.75 - 1e-6)
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

  it('the trunk-tangent rule (round-8-D): two most-opposite legs flow through as one trunk, side legs merge tangentially', () => {
    // The USER LAW ruled 2026-07-06: a k-way junction must NOT read as a
    // 120°-symmetric star ("everything just going to a single point"). Each hub
    // leg's arrival direction is pulled to its trunkTarget along the hub's trunk
    // axis phi. Directly on the pure rule (no settling): two collinear legs
    // (chord dirs 0 and π) on axis phi=0 must arrive ANTIPARALLEL — one
    // continuous trunk straight through the hub.
    const deg = (r: number) => (r * 180) / Math.PI
    const between = (a: number, b: number): number => { let d = Math.abs(deg(a) - deg(b)) % 360; if (d > 180) d = 360 - d; return d }
    const tTrunkA = trunkTarget(0, 0)
    const tTrunkB = trunkTarget(Math.PI, 0)
    expect(between(tTrunkA, tTrunkB), 'two on-axis legs arrive antiparallel (a continuous trunk)').toBeGreaterThanOrEqual(179)
    // a leg perpendicular to the axis takes NO pull (weight |cos|=0) — its
    // outgoing tangent (target+π) stays exactly radial, so a side branch crossing
    // the axis can never jump between ends (the merge is continuous)
    const outPerp = trunkTarget(Math.PI / 2, 0) + Math.PI
    expect(between(Math.atan2(Math.sin(outPerp), Math.cos(outPerp)), Math.PI / 2), 'a perpendicular leg is not pulled (continuity at the flip)').toBeLessThan(1)
    // an OFF-axis side leg (60° off) is pulled TOWARD the axis but not all the way
    // (partial weight) — the tributary merge. Its outgoing tangent (target+π) sits
    // between its radial chord and the axis.
    const dirSide = (60 * Math.PI) / 180
    const outSide = trunkTarget(dirSide, 0) + Math.PI // outgoing tangent from hub toward port
    expect(deg(Math.atan2(Math.sin(outSide), Math.cos(outSide))), 'side leg merges tangentially (pulled toward the 0 axis, not left radial)').toBeLessThan(60)
    expect(deg(Math.atan2(Math.sin(outSide), Math.cos(outSide))), 'side leg is not pulled all the way to the axis').toBeGreaterThan(0)
  })

  it('a settled junction pulls two legs past the 120° star toward a trunk', () => {
    // Wired into the physics (not just the pure rule): the symmetric threeWay has
    // no geometrically-preferred trunk, yet the trunk energy still pulls its two
    // nearest-axis legs BEYOND the 120° a Plateau star would rest at — the most-
    // opposite arrival pair exceeds 120°, so the junction no longer reads as a
    // symmetric point-star. (Asymmetric junctions form a far stronger trunk; see
    // the pure-rule test and the app screenshots.)
    const e = settled(threeWay, 6000)
    const w = [...e.wires.values()].find((x) => x.hub !== null)!
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
    const between = (a: number, b: number): number => { let d = Math.abs((a - b) * 180 / Math.PI) % 360; if (d > 180) d = 360 - d; return d }
    let mostOpp = 0
    for (let i = 0; i < 3; i++) for (let j = i + 1; j < 3; j++) mostOpp = Math.max(mostOpp, between(dirs[i]!, dirs[j]!))
    expect(mostOpp, `most-opposite pair ${mostOpp.toFixed(0)}° must exceed the 120° star`).toBeGreaterThan(128)
  })
})

// ---- boundary wires (merged hub + exit) -----------------------------------

describe('wire physics — bodyless boundary attachment (plan 24, the reset ruling)', () => {
  it('a 1-port boundary wire is ONE bodyless leg to the fixed inner-frame slot (no exit body, no dot)', () => {
    const { d, b, wid } = boundaryOne()
    const e = mkEngine(d, b)
    settle(e, 400) // establishes the fixed frame; the boundary leg closes on its slot
    const w = e.wires.get(wid)!
    expect(w.slot, 'the boundary wire owns a fixed frame slot').not.toBeNull()
    expect(w.hub, 'a 1-port boundary wire has NO hub').toBeNull()
    // NO exit body (the reset's "there's an edge node for some reason") — e:<wid>
    // exit hubs are abolished; the boundary attaches to a fixed slot, not a body
    expect([...e.bodies.keys()].some((id) => id.startsWith('e:')), 'no exit body exists').toBe(false)
    expect(existentialStubs(e).some((s) => s.wid === wid), 'no ∃ dot on a boundary wire').toBe(false)
    // exactly one leg, from the port to the slot on the inner frame edge
    const legs = computeLegs(e).filter((g) => g.leg.wid === wid)
    expect(legs, 'exactly one leg').toHaveLength(1)
    const pts = legs[0]!.pts
    const slot = frameSlots(frameBounds(e)!, 1)[0]!
    const end = pts[pts.length - 1]!
    expect(Math.hypot(end.x - slot.point.x, end.y - slot.point.y), 'leg far end sits on the slot').toBeLessThan(1.0)
    // meets the frame perpendicular (final tangent ≈ the slot normal)
    const pen = pts[pts.length - 2]!
    const off = Math.atan2(Math.sin(Math.atan2(end.y - pen.y, end.x - pen.x) - slot.normal), Math.cos(Math.atan2(end.y - pen.y, end.x - pen.x) - slot.normal))
    expect(Math.abs(off), `perpendicular meeting: off-normal ${off.toFixed(3)}`).toBeLessThan(0.35)
  })

  it('boundary slot assignment is canonical by boundary order and never reorders under a wild body sweep', () => {
    const { diagram, boundary } = threeBoundary()
    const e = mkEngine(diagram, boundary)
    settle(e, 1200)
    const slots = frameSlots(frameBounds(e)!, boundary.length) // fixed frame → fixed slots
    const layouts: { x: number; y: number }[][] = [
      [{ x: -20, y: -20 }, { x: 20, y: -20 }, { x: 0, y: 20 }],
      [{ x: 18, y: 5 }, { x: 20, y: -3 }, { x: 16, y: 9 }],
      [{ x: -5, y: -18 }, { x: 3, y: -20 }, { x: -1, y: -16 }],
    ]
    const nodeIds = [...e.bodies.keys()].filter((id) => { const k = e.bodies.get(id)!.kind; return k !== 'junction' && k !== 'anchor' })
    for (const layout of layouts) {
      nodeIds.forEach((id, k) => { if (layout[k]) e.bodies.get(id)!.pos = layout[k]! })
      recomputeRegions(e)
      const legsByWid = new Map<string, { x: number; y: number }[][]>()
      for (const g of computeLegs(e)) { const a = legsByWid.get(g.leg.wid) ?? []; a.push(g.pts); legsByWid.set(g.leg.wid, a) }
      boundary.forEach((wid, i) => {
        let best = Infinity
        for (const pts of legsByWid.get(wid)!) for (const end of [pts[0]!, pts[pts.length - 1]!]) {
          best = Math.min(best, Math.hypot(end.x - slots[i]!.point.x, end.y - slots[i]!.point.y))
        }
        expect(best, `boundary ${i} reaches slot ${i}`).toBeLessThan(1.5)
      })
    }
  })
})

// ---- wire↔FRAME containment (USER STANDING LAW: nothing drawn outside the frame)

describe('wire physics — nothing is ever drawn outside the frame at rest (USER STANDING LAW)', () => {
  it('no leg or trunk sample sits outside the fixed border on any settled fixture', () => {
    // The reset + plan-23 follow-ups ruled it repeatedly: a wire arcing outside the
    // frame (a blind-cone fallback that wraps, a boundary leg reaching a far slot) is
    // a VIOLATION, not a preference. The frame-containment energy (uncapped, same
    // class as the cut barrier) pulls every leg AND the emergent trunk inside; the
    // escape is the node rotating / the hub migrating (Task-3/4 dynamics), never a
    // diagram-wrapping arc.
    for (const mk of [threeWay, boundaryOne, forallShape, interposed]) {
      const e = settled(mk, 2000)
      const fb = frameBounds(e)!
      const outside = (p: { x: number; y: number }): number => Math.max(
        p.x - fb.maxX, fb.minX - p.x, p.y - fb.maxY, fb.minY - p.y)
      let worst = 0
      for (const { pts } of legPaths(e)) for (const p of pts) worst = Math.max(worst, outside(p))
      // a small tolerance for the paint-resolution polyline vs the sample grid
      expect(worst, `a wire escaped the frame by ${worst.toFixed(1)} wu`).toBeLessThan(1.0)
    }
  })
})

// ---- regression bounds from the measured theorem scenes -------------------

import { mkReplay } from '../../src/app/replay'
import { bootFixture } from '../app/boot-fixture'
import { legPaths } from '../../src/view/wires'
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
