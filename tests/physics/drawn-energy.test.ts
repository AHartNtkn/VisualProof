import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { DISC_R, ROUTE_CLEAR, mkEngine, escapePoint, routeObstacles, routeBounds, wireTerminalPoints, wireTerminalBCs } from '../../src/view/engine'
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
      const pts = edgeCurvePts(u < bcs.length ? bcs[u]! : null, v < bcs.length ? bcs[v]! : null, r.pts, ROUTE_CLEAR * e.scale)
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

  it('a forced U-turn rests in the FAMILY: no kinks, radius at the pinned family floor', () => {
    // one node, its two ports wired to each other: a net turn near π that no
    // rotation can remove. The bound is the FAMILY's measured resting floor on
    // this fixture (1.62 wu) with 20% slack — the family law defines gentle,
    // not a rod-physics derivation. Kink bound: no adjacent-sample turn > π/4.
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
    for (const leg of computeLegs(e)) {
      expect(minRadius(leg.pts), 'U rests at the family floor').toBeGreaterThanOrEqual(1.3)
      for (let k = 1; k + 1 < leg.pts.length; k++) {
        const d0 = Math.atan2(leg.pts[k]!.y - leg.pts[k - 1]!.y, leg.pts[k]!.x - leg.pts[k - 1]!.x)
        const d1 = Math.atan2(leg.pts[k + 1]!.y - leg.pts[k]!.y, leg.pts[k + 1]!.x - leg.pts[k]!.x)
        const turn = Math.abs(Math.atan2(Math.sin(d1 - d0), Math.cos(d1 - d0)))
        expect(turn, `kink at sample ${k}`).toBeLessThan(Math.PI / 4)
      }
    }
  })

  it('corridor simplification: sub-clearance corner noise cannot change the curve', () => {
    const u = { p: { x: 0, y: 0 }, n: { x: 1, y: 0 } }
    const clean = [{ x: 3, y: 0 }, { x: 20, y: 6 }, { x: 40, y: 6 }]
    const noisy = [{ x: 3, y: 0 }, { x: 20, y: 6 }, { x: 20.4, y: 6.2 }, { x: 40, y: 6 }]
    // DP's contract is a deviation band, not bit-identity: the noisy corner
    // may replace its clean neighbor WITHIN the tolerance — the two curves
    // must stay inside the clearance band of each other
    const a = edgeCurvePts(u, null, clean, 1.5)
    const bb = edgeCurvePts(u, null, noisy, 1.5)
    expect(bb.length).toBe(a.length)
    for (let i = 0; i < a.length; i++) {
      expect(Math.hypot(a[i]!.x - bb[i]!.x, a[i]!.y - bb[i]!.y)).toBeLessThanOrEqual(1.5)
    }
  })
})

describe('family conformance (coverage artifact): the drawn legs ARE Hobby cubics', () => {
  /** Fit one cubic Bézier to samples taken at known parameters t=j/S by
      linear least squares; a true cubic fits exactly. */
  function cubicResidual(span: readonly Vec2[]): number {
    const S = span.length - 1
    const B = (i: number, t: number): number => {
      const u = 1 - t
      return [u * u * u, 3 * u * u * t, 3 * u * t * t, t * t * t][i]!
    }
    const AtA: number[][] = Array.from({ length: 4 }, () => new Array<number>(4).fill(0))
    const Atx = new Array<number>(4).fill(0)
    const Aty = new Array<number>(4).fill(0)
    for (let j = 0; j <= S; j++) {
      const t = j / S
      for (let i = 0; i < 4; i++) {
        for (let k = 0; k < 4; k++) AtA[i]![k]! += B(i, t) * B(k, t)
        Atx[i]! += B(i, t) * span[j]!.x
        Aty[i]! += B(i, t) * span[j]!.y
      }
    }
    const solve = (rhs: number[]): number[] => {
      const M = AtA.map((row, i) => [...row, rhs[i]!])
      for (let c = 0; c < 4; c++) {
        let piv = c
        for (let r2 = c + 1; r2 < 4; r2++) if (Math.abs(M[r2]![c]!) > Math.abs(M[piv]![c]!)) piv = r2
        ;[M[c], M[piv]] = [M[piv]!, M[c]!]
        for (let r2 = 0; r2 < 4; r2++) {
          if (r2 === c) continue
          const f = M[r2]![c]! / M[c]![c]!
          for (let k = c; k < 5; k++) M[r2]![k]! -= f * M[c]![k]!
        }
      }
      return M.map((row, i2) => row[4]! / M[i2]![i2]!)
    }
    const cx = solve(Atx), cy = solve(Aty)
    let worst = 0
    for (let j = 0; j <= S; j++) {
      const t = j / S
      let px = 0, py = 0
      for (let i = 0; i < 4; i++) { px += B(i, t) * cx[i]!; py += B(i, t) * cy[i]! }
      worst = Math.max(worst, Math.hypot(px - span[j]!.x, py - span[j]!.y))
    }
    return worst
  }

  it('every drawn span of a settled scene is exactly one cubic; clamped exits align with the port normal', () => {
    const b = new DiagramBuilder()
    const n0 = b.ref(b.root, 'A', relSig([TERM]))
    const n1 = b.ref(b.root, 'B', relSig([TERM]))
    b.wire(b.root, [
      { node: n0, port: { kind: 'arg' as const, index: 0 } },
      { node: n1, port: { kind: 'arg' as const, index: 0 } },
    ])
    const e = mkEngine(b.build(), [])
    recomputeRegions(e)
    resolveOverlaps(e)
    const t0 = performance.now()
    for (let i = 0; i < 100000; i++) {
      if (!settleStep(e)) break
      if (performance.now() - t0 > 20000) break
    }
    const SUB = 7
    for (const leg of computeLegs(e)) {
      expect((leg.pts.length - 1) % SUB, 'sample count is whole cubic spans').toBe(0)
      for (let s0 = 0; s0 + SUB < leg.pts.length; s0 += SUB) {
        const span = leg.pts.slice(s0, s0 + SUB + 1)
        expect(cubicResidual(span), `span at ${s0} is a cubic`).toBeLessThan(1e-6)
      }
    }
    for (const [, w] of e.wires) {
      for (const bd of w.binds) {
        const body = e.bodies.get(bd.body)!
        const la = body.localAnchor.get(bd.key)!
        const normal = Math.atan2(la.y, la.x) + body.theta
        const leg = computeLegs(e).find((g) => g.leg.from.body === bd.body)
        if (leg === undefined) continue
        const dir = Math.atan2(leg.pts[1]!.y - leg.pts[0]!.y, leg.pts[1]!.x - leg.pts[0]!.x)
        const off = Math.abs(Math.atan2(Math.sin(dir - normal), Math.cos(dir - normal)))
        expect(off, 'clamped exit along the port normal').toBeLessThan(Math.PI / 8)
      }
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
