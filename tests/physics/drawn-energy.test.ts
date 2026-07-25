import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { DISC_R, mkEngine, escapePoint, routeObstacles, routeBounds, wireTerminalPoints, wireTerminalBCs } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { wireEnergy, settleStep, recomputeRegions, resolveOverlaps, segSeparationE } from '../../src/view/relax'
import type { Vec2 } from '../../src/view/vec'
import { mkFreeSpace, route } from '../../src/view/route/freespace'
import { edgeCurvePts, rodCost } from '../../src/view/route/curve'
import { computeLegs } from '../../src/view/wires'

/**
 * THE ROD-ENERGY LAW (USER ruling 2026-07-24: "the minimal energy curves
 * should be gentle... the energy function for the curve shapes is simply
 * wrong — rethink it from first principles"): the wire energy is the elastic
 * rod functional ∫(α + β·κ²)ds over the DRAWN curve (plus the soft
 * obstacle/frame surcharges and separation). A total-turn charge is
 * placement-invariant, so its minimizers are straight polylines with point
 * corners — the rejected look. κ² makes turning spread: the minimizers bend
 * at the characteristic radius r* = √(β/α) = the node-disc scale.
 */

/** The expected energy recomputed from primitives exactly as the renderer
    assembles the stroke: per edge, the Hermite curve through the route
    waypoints with the terminal boundary conditions, charged by rodCost. */
function drawnWireCost(e: Engine): number {
  const space = { discs: routeObstacles(e), bounds: routeBounds(e) }
  const fs = mkFreeSpace(space.discs, space.bounds)
  const beta = (DISC_R * e.scale) ** 2
  let E = 0
  const segs: { wid: string; a: Vec2; b: Vec2 }[] = []
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    const bcs = wireTerminalBCs(e, w)
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    for (const [u, v] of w.net.edges) {
      const r = route(fs, pos(u), pos(v))
      const pts = edgeCurvePts(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, r.pts, space, beta)
      E += rodCost(pts, space, beta)
      for (let i = 0; i + 1 < pts.length; i++) segs.push({ wid, a: pts[i]!, b: pts[i + 1]! })
    }
  }
  return E + segSeparationE(segs, e.scale)
}

/** Minimum discrete curvature radius along a sampled stroke (Δs̄/Δθ). */
function minRadius(pts: readonly { x: number; y: number }[]): number {
  let r = Infinity
  for (let i = 1; i + 1 < pts.length; i++) {
    const ax = pts[i]!.x - pts[i - 1]!.x, ay = pts[i]!.y - pts[i - 1]!.y
    const bx = pts[i + 1]!.x - pts[i]!.x, by = pts[i + 1]!.y - pts[i]!.y
    const la = Math.hypot(ax, ay), lb = Math.hypot(bx, by)
    if (la < 1e-9 || lb < 1e-9) continue
    const dot = Math.max(-1, Math.min(1, (ax * bx + ay * by) / (la * lb)))
    const dth = Math.acos(dot)
    if (dth < 1e-6) continue
    r = Math.min(r, (la + lb) / 2 / dth)
  }
  return r
}

describe('wire energy is the rod energy of the DRAWN curve', () => {
  it('needle at a port: energy identity holds with the dot on the stub', () => {
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'A', relSig([TERM]))
    b.wire(b.root, [{ node: n, port: { kind: 'arg' as const, index: 0 } }])
    const e = mkEngine(b.build(), [])
    const A = [...e.bodies.values()].find((x) => x.kind === 'ref')!
    A.pos = { x: 0, y: 0 }
    A.theta = 0
    e.frame = null
    recomputeRegions(e)
    const w = [...e.wires.values()][0]!
    const { anchor, escape } = escapePoint(e, w.binds[0]!)
    const dot = e.bodies.get(w.endBodyId!)!
    dot.pos = { x: (anchor.x + escape.x) / 2, y: (anchor.y + escape.y) / 2 }
    recomputeRegions(e)
    const drawn = drawnWireCost(e)
    const E = wireEnergy(e)
    expect(Math.abs(E - drawn)).toBeLessThan(1e-6 * (Math.abs(drawn) + 1))
  })

  it('facing-away port: energy identity holds through the forced turn', () => {
    const b = new DiagramBuilder()
    const n0 = b.ref(b.root, 'A', relSig([TERM]))
    const n1 = b.ref(b.root, 'B', relSig([TERM]))
    b.wire(b.root, [
      { node: n0, port: { kind: 'arg' as const, index: 0 } },
      { node: n1, port: { kind: 'arg' as const, index: 0 } },
    ])
    const e = mkEngine(b.build(), [])
    const bodies = [...e.bodies.values()].filter((x) => x.kind === 'ref')
    const A = bodies[0]!, B = bodies[1]!
    A.pos = { x: -80, y: 0 }; B.pos = { x: 80, y: 0 }
    const angOf = (bd: typeof A): number => {
      const la = [...bd.localAnchor.values()][0]!
      return Math.atan2(la.y, la.x)
    }
    A.theta = Math.PI - angOf(A)
    B.theta = Math.PI - angOf(B)
    e.frame = null
    recomputeRegions(e)
    const drawn = drawnWireCost(e)
    const E = wireEnergy(e)
    expect(Math.abs(E - drawn)).toBeLessThan(1e-6 * (Math.abs(drawn) + 1))
  })

  it('a forced U-turn rests GENTLE: min curvature radius ≥ half the node scale', () => {
    // one node, its two ports wired to each other: the drawn curve must leave
    // one port and arrive at the other — a net turn near π that no rotation
    // can remove. Under the rod energy the turn spreads at radius ~r*; a
    // total-turn energy leaves it concentrated in tight fillet corners.
    // (bound = r*/2: within discretization slack of the derived radius)
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'A', relSig([TERM, TERM]))
    b.wire(b.root, [
      { node: n, port: { kind: 'arg' as const, index: 0 } },
      { node: n, port: { kind: 'arg' as const, index: 1 } },
    ])
    const e = mkEngine(b.build(), [])
    recomputeRegions(e)
    resolveOverlaps(e)
    const t0 = performance.now()
    for (let i = 0; i < 100000; i++) {
      if (!settleStep(e)) break
      if (performance.now() - t0 > 20000) break
    }
    const rStar = DISC_R * e.scale
    for (const leg of computeLegs(e)) {
      const r = minRadius(leg.pts)
      expect(r, `stroke bends at radius ${r.toFixed(2)} < r*/2 = ${(rStar / 2).toFixed(2)}`).toBeGreaterThanOrEqual(rStar / 2)
    }
  })
})

describe('envelope probe evaluator (frozen corridors)', () => {
  it('frozen eval equals the exact energy at the captured base (real replay scenes)', async () => {
    const { wireEnergyCapture, frozenWireEnergy } = await import('../../src/view/relax')
    const { bootFixture } = await import('../app/boot-fixture')
    const { mkReplay } = await import('../../src/app/replay')
    const ctx = (await bootFixture()).ctx
    for (const [nm, at] of [['plusComm', 20], ['succShiftS', 48]] as const) {
      const r = mkReplay(nm, ctx)
      const e = mkEngine(r.diagramAt(at), r.boundaryAt(at))
      recomputeRegions(e)
      resolveOverlaps(e)
      const cap = wireEnergyCapture(e)
      const frozen = frozenWireEnergy(e, cap.edges)
      expect(Math.abs(frozen - cap.E), `${nm}@${at}: frozen != exact at base`).toBeLessThan(1e-9 * (Math.abs(cap.E) + 1))
    }
  })
})
