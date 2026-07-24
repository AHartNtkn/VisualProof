import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
/** An n-ary relation signature over individuals (ref/atom arity, new sig API). */
const rel = (n: number) => relSig(Array.from({ length: n }, () => TERM))
import type { Diagram, WireId } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine, worldBindAnchor, resolveLeg, traceLeg, frameBounds, frameSlots, type Engine, type WireView, type WireLeg } from '../../src/view/engine'
import { settle, settleStep, wireEnergy, WIREP, totalEnergy, recomputeRegions } from '../../src/view/relax'
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
  const r1 = b.ref(b.root, 'plus', rel(3))
  const r2 = b.ref(b.root, 'times', rel(3))
  const r3 = b.ref(b.root, 'succ', rel(2))
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
  const n = b.ref(b.root, 'nat', rel(1))
  const w = b.wire(b.root, [{ node: n, port: { kind: 'arg', index: 0 } }])
  return { d: b.build(), b: [], node: n, wid: w }
}

/** The ∀ shape: 2-endpoint wire inside a cut, scoped at root — the dangle
    branch reaches a scope-homed via-body hub. */
function forallShape(): { d: Diagram; b: WireId[]; wid: WireId } {
  const b = new DiagramBuilder()
  const cut = b.cut(b.root)
  const r1 = b.ref(cut, 'lt', rel(2))
  const r2 = b.ref(cut, 'gt', rel(2))
  const w = b.wire(b.root, [
    { node: r1, port: { kind: 'arg', index: 0 } },
    { node: r2, port: { kind: 'arg', index: 0 } },
  ])
  return { d: b.build(), b: [], wid: w }
}

/** Crowded: a 2-ender forced to route past an interposed disc. */
function interposed(): { d: Diagram; b: WireId[] } {
  const b = new DiagramBuilder()
  const r1 = b.ref(b.root, 'a', rel(1))
  const r2 = b.ref(b.root, 'b', rel(1))
  b.ref(b.root, 'wall', rel(1))
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
  const n = b.ref(b.root, 'p', rel(1))
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

// A fixture settled to its FIXED POINT, memoized by fixture name and SHARED across
// every read-only law assertion. The plan-24 fixed-point stop makes one settle reach
// rest (every fixture here converges in <300 ticks, far under the caps these tests
// used), so all read-only tests observe the IDENTICAL resting engine — sharing
// changes WHEN it is settled, never WHAT is read. Tests that MUTATE after settling
// (the E-band + no-orbit observation loops, the purity orbit attack, the dangle-tow
// drag, the boundary slot sweep) build their OWN engine via `settled` / mkEngine.
const sharedCache = new Map<string, Engine>()
const sharedSettled = (mk: () => { d: Diagram; b: WireId[] }): Engine => {
  let e = sharedCache.get(mk.name)
  if (e === undefined) { e = settled(mk, 8000); sharedCache.set(mk.name, e) }
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
      const e = sharedSettled(mk)
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
      const e = sharedSettled(mk)
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
    const branches = [...e.wires].map(([wid, w]) => [wid, w.branches.map((p) => ({ ...p }))] as const)
    const angles = [...e.wires].map(([wid, w]) => [wid, w.legs.map((l) => [l.angA, l.angB] as const)] as const)
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
    for (const [wid, bs] of branches) { const w = e.wires.get(wid)!; w.branches.forEach((_, i) => { w.branches[i] = { ...bs[i]! } }) }
    for (const [wid, as] of angles) { const w = e.wires.get(wid)!; w.legs.forEach((l, i) => { l.angA = as[i]![0]; l.angB = as[i]![1] }) }
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
      const e = sharedSettled(mk)
      for (const g of computeLegs(e)) {
        const w = e.wires.get(g.leg.wid)!
        const bind = w.binds.find((bd) => bd.body === g.leg.from.body && bd.key === g.leg.from.key)
        if (bind === undefined) continue // interior end
        const body = e.bodies.get(bind.body)!
        const anchor = worldBindAnchor(e, body, bind.key)
        expect(Math.hypot(g.pts[0]!.x - anchor.x, g.pts[0]!.y - anchor.y), 'starts on rim').toBeLessThan(1e-6)
        const la = body.localAnchor.get(bind.key)!
        const normal = Math.atan2(la.y, la.x) + body.theta
        // Measure the exit direction from a FINE trace of the leg's first segment,
        // NOT the coarse computeLegs chord (g.pts). The exit tangent θ(0) is the
        // port normal EXACTLY by rim-lock construction; the drawn first-segment
        // chord deviates from it by ≈ c1/(2·QN), i.e. in proportion to the leg's
        // CURVATURE, not its true exit angle. The coarse QN over-reports a hard-
        // curving leg (a near-blind-cone ∃ tip in the max-crowd threeWay, c1≈5,
        // reads ~0.055) even though it leaves perpendicular; the fine trace
        // isolates the real exit direction (that same leg: 0.0125), so the tight
        // 0.05 bound measures the LAW instead of the sampler.
        const leg = w.legs.find((l) => l.a.kind === 'bind' && w.binds[l.a.i]?.body === bind.body && w.binds[l.a.i]?.key === bind.key)!
        const sol = resolveLeg(e, w, leg)
        const fine: { x: number; y: number }[] = []
        traceLeg(sol, fine, 200)
        const dirFine = Math.atan2(fine[1]!.y - fine[0]!.y, fine[1]!.x - fine[0]!.x)
        const dev = Math.atan2(Math.sin(dirFine - normal), Math.cos(dirFine - normal))
        expect(Math.abs(dev), `exit at ${bind.body}:${bind.key} (range ${thetaRange(sol.sol.c1, sol.sol.c2).toFixed(2)})`).toBeLessThanOrEqual(0.05)
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
    const { wid } = dangling()
    const e = sharedSettled(dangling)
    const w = e.wires.get(wid)!
    const tip = e.bodies.get(w.endBodyId!)!
    const bd = w.binds[0]!
    const anchor = worldBindAnchor(e, e.bodies.get(bd.body)!, bd.key)
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
    const tip = e.bodies.get(e.wires.get(wid)!.endBodyId!)!
    const gapBefore = Math.hypot(tip.pos.x - body.pos.x, tip.pos.y - body.pos.y)
    const tipStart = { ...tip.pos }
    // move the node a MODEST, in-regime amount and PIN it there — the real drag
    // path (settleStep's pinned set). An UNPINNED move is not a tow test: an
    // unanchored node relaxes back toward its own rest, so the tip barely moves;
    // and an over-large shove (≫ the rest gap) drives the pinned node against its
    // containment wall (which the live app's drag clamp prevents), a degenerate
    // regime. Held at a sane displacement, the wire's tension must TOW the free
    // end along so the rest length re-establishes at the node's new position.
    const DISP = 8 // < the 11.5 rest gap: comfortably in-regime
    body.pos = { x: body.pos.x + DISP, y: body.pos.y }
    const pin = new Set([node])
    for (let i = 0; i < 4000; i++) settleStep(e, pin)
    // (1) the free end FOLLOWED the node's move — DIRECTIONALLY. Its net
    //     displacement has a positive component along the node's move (+x); it
    //     tracked the node, not drifted opposite or frozen. NOT a magnitude floor:
    //     the node ROTATES freely to face the tip (drag-rotation is desired), which
    //     relieves tension and legitimately shares the work, so the tip tows LESS
    //     than the full displacement (measured tow ≈ 2.2, node rotates ≈ 33°). A
    //     magnitude floor would falsely fail this correct rotation-assisted rest.
    const followX = tip.pos.x - tipStart.x
    expect(followX, `the free end must track the node's move, not freeze/reverse (moved ${followX.toFixed(2)} in x)`).toBeGreaterThan(0.5)
    // (2) the REST SHAPE restored: the wire re-establishes its rest length at the
    //     node's new location (both ends participate — the core dangle-tow law).
    const gapAfter = Math.hypot(tip.pos.x - body.pos.x, tip.pos.y - body.pos.y)
    expect(Math.abs(gapAfter - gapBefore), `rest length must restore (${gapAfter.toFixed(2)} vs ${gapBefore.toFixed(2)})`).toBeLessThanOrEqual(gapBefore * 0.2)
  })

  it('a settled branch junction sits at a strict energy minimum over its branch point + tangents', () => {
    // WAS: "a settled branch junction pulls two legs past the 120° star toward a
    // trunk" (asserted the most-opposite pair > 128°). That codified the trunk-
    // tributary AESTHETIC via the removed `trunkTarget` clamp — a look the user has
    // since said was NEVER law ("I never made a trunk tributary model law"). The
    // SCENE is preserved as a fixture; the assertion is rewritten to the energy LAW
    // the freed-tangent junction actually obeys: the settled branch point and its
    // free leg tangents are a strict local minimum of the total energy (no probe
    // lowers it). The specific meeting ANGLE is deferred to the user's visual ruling
    // (see .superpowers/sdd/junction-gallery), so no angle is asserted here.
    const e = sharedSettled(threeWay)
    const w = [...e.wires.values()].find((x) => x.branches.length > 0)!
    expect(w.branches, 'the three-way interior junction is a branch tree').toHaveLength(1)
    const E0 = totalEnergy(e)
    const NOISE = 1e-4 * (Math.abs(E0) + 1)
    const sc = e.scale
    const b0 = { ...w.branches[0]! }
    let minPos = 0
    for (let ix = -3; ix <= 3; ix++) for (let iy = -3; iy <= 3; iy++) {
      if (ix === 0 && iy === 0) continue
      w.branches[0] = { x: b0.x + ix * sc, y: b0.y + iy * sc }
      minPos = Math.min(minPos, totalEnergy(e) - E0)
    }
    w.branches[0] = b0
    expect(minPos, `a branch-position perturbation lowered E by ${(-minPos).toFixed(4)} — not a strict minimum`).toBeGreaterThanOrEqual(-NOISE)
    let minTan = 0
    for (const leg of w.legs) {
      if (leg.b.kind !== 'branch') continue
      const a0 = leg.angB
      for (const d of [-0.3, -0.15, -0.05, 0.05, 0.15, 0.3]) { leg.angB = a0 + d; minTan = Math.min(minTan, totalEnergy(e) - E0) }
      leg.angB = a0
    }
    expect(minTan, `a leg-tangent perturbation lowered E by ${(-minTan).toFixed(4)} — not a strict minimum`).toBeGreaterThanOrEqual(-NOISE)
  })
})

// ---- boundary wires (merged hub + exit) -----------------------------------

describe('wire physics — bodyless boundary attachment (plan 24, the reset ruling)', () => {
  it('a 1-port boundary wire is ONE bodyless leg to the fixed inner-frame slot (no exit body, no dot)', () => {
    const { wid } = boundaryOne()
    const e = sharedSettled(boundaryOne)
    const w = e.wires.get(wid)!
    expect(w.slots, 'the boundary wire owns its fixed frame incidence').toEqual([0])
    expect(w.endBodyId, 'a 1-port boundary wire has NO end body').toBeNull()
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
    const nodeIds = [...e.bodies.keys()].filter((id) => { const k = e.bodies.get(id)!.kind; return k !== 'end' && k !== 'anchor' })
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

  it('a repeated boundary identity traces one line between both shifted frame incidences', () => {
    const h = new DiagramBuilder()
    const shared = h.wire(h.root, [])
    const other = h.wire(h.root, [])
    const e = mkEngine(h.build(), [shared, other, shared])
    settle(e, 20)
    e.slotShift = 1

    const leg = computeLegs(e).filter((g) => g.leg.wid === shared)
    expect(leg).toHaveLength(1)
    const physical = frameSlots(frameBounds(e)!, 3)
    const ends = [leg[0]!.pts[0]!, leg[0]!.pts[leg[0]!.pts.length - 1]!]
    for (const logical of [0, 2]) {
      const target = physical[(logical + e.slotShift) % 3]!.point
      expect(Math.min(...ends.map((point) => Math.hypot(point.x - target.x, point.y - target.y)))).toBeLessThan(1)
    }
  })

  it('an attached repeated-boundary wire reaches both slots and its node port', () => {
    const h = new DiagramBuilder()
    const n = h.termNode(h.root, parseTerm('\\x. x'))
    const shared = h.wire(h.root, [{ node: n, port: { kind: 'output' } }])
    const e = mkEngine(h.build(), [shared, shared])
    settle(e, 200)

    const legs = computeLegs(e).filter((g) => g.leg.wid === shared)
    const endpoints = legs.flatMap((leg) => [leg.pts[0]!, leg.pts[leg.pts.length - 1]!])
    for (const slot of frameSlots(frameBounds(e)!, 2)) {
      expect(Math.min(...endpoints.map((point) => Math.hypot(point.x - slot.point.x, point.y - slot.point.y)))).toBeLessThan(1)
    }
    const port = worldBindAnchor(e, e.bodies.get(n)!, 'out')
    expect(Math.min(...endpoints.map((point) => Math.hypot(point.x - port.x, point.y - port.y)))).toBeLessThan(1)
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
      const e = sharedSettled(mk)
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
  const r = mkReplay('plusComm', bootCtx)
  return { diagram: r.diagramAt(0), boundary: r.boundaryAt(0) }
}
function mkArgs(mk: () => { d: Diagram; b: WireId[] }): [Diagram, WireId[]] {
  const { d, b } = mk()
  return [d, b]
}

void ELASTICA
