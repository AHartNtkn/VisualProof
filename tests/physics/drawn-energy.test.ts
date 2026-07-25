import { describe, it, expect } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { relSig, TERM } from '../../src/kernel/diagram/sig'
import { mkEngine, escapePoint, slotEscape, routeObstacles, routeBounds, wireTerminalPoints } from '../../src/view/engine'
import type { Engine } from '../../src/view/engine'
import { wireEnergy, recomputeRegions, segSeparationE } from '../../src/view/relax'
import type { Vec2 } from '../../src/view/vec'
import { mkFreeSpace, route, polylineTurning } from '../../src/view/route/freespace'
import { BEND_COST } from '../../src/view/route/network'

/**
 * THE DRAWN-STROKE ENERGY LAW (USER rulings 2026-07-24: "everything onto the
 * energy function"; a 180° hairpin is among the costliest configurations; the
 * angles of the nodes are calculated along with the curves): the wire energy
 * charges what is DRAWN. Every stroke is stub + route + stub; its turning —
 * including the bends where the fixed stubs meet the routed path — is charged
 * at BEND_COST per radian. An energy that charges only the route's interior
 * turning is blind to the port hairpin (stub out, route doubling straight
 * back is free), which is exactly the resting needle/loop defect observed in
 * the app on 2026-07-24.
 */

/** The expected energy of a wire, recomputed from primitives exactly as the
    renderer assembles the stroke: per edge, soft route cost + BEND_COST ×
    turning of [stub?, ...route pts, stub?]. */
function drawnWireCost(e: Engine): number {
  const fs = mkFreeSpace(routeObstacles(e), routeBounds(e))
  let E = 0
  const segs: { wid: string; a: Vec2; b: Vec2 }[] = []
  for (const [wid, w] of e.wires) {
    const terms = wireTerminalPoints(e, w)
    if (terms.length < 2) continue
    const pos = (v: number): Vec2 => (v < terms.length ? terms[v]! : w.net.junctions[v - terms.length]!)
    const stub = (v: number): Vec2 | null => {
      if (v < w.binds.length) return escapePoint(e, w.binds[v]!).anchor
      if (v < w.binds.length + w.slots.length) return slotEscape(e, w.slots[v - w.binds.length]!)?.point ?? null
      return null
    }
    for (const [u, v] of w.net.edges) {
      const r = route(fs, pos(u), pos(v))
      const su = stub(u), sv = stub(v)
      const pts = [...(su !== null ? [su] : []), ...r.pts, ...(sv !== null ? [sv] : [])]
      E += r.cost + BEND_COST * polylineTurning(pts)
      for (let i = 0; i + 1 < r.pts.length; i++) segs.push({ wid, a: r.pts[i]!, b: r.pts[i + 1]! })
    }
  }
  return E + segSeparationE(segs, e.scale)
}

describe('wire energy charges the DRAWN stroke (stubs included)', () => {
  it('needle at a port: dot between anchor and escape — the 180° stub hairpin must be charged', () => {
    // one node with a single port, wire ending in a free ∃ dot
    const b = new DiagramBuilder()
    const n = b.ref(b.root, 'A', relSig([TERM]))
    b.wire(b.root, [{ node: n, port: { kind: 'arg' as const, index: 0 } }])
    const d = b.build()
    const e = mkEngine(d, [])
    const A = [...e.bodies.values()].find((x) => x.kind === 'ref')!
    A.pos = { x: 0, y: 0 }
    A.theta = 0
    e.frame = null
    recomputeRegions(e)
    const w = [...e.wires.values()][0]!
    expect(w.endBodyId).not.toBeNull()
    // place the dot ON the stub, between the rim anchor and the escape point:
    // the route (escape → dot) is a short straight double-back over the stub —
    // the drawn stroke has a ~π hairpin at the escape point
    const { anchor, escape } = escapePoint(e, w.binds[0]!)
    const dot = e.bodies.get(w.endBodyId!)!
    dot.pos = { x: (anchor.x + escape.x) / 2, y: (anchor.y + escape.y) / 2 }
    recomputeRegions(e)

    const drawn = drawnWireCost(e)
    const E = wireEnergy(e)
    // the hairpin is worth ~BEND_COST·π ≈ 25; the identity must hold to float
    // tolerance — an energy below the drawn cost is blind to a drawn bend
    expect(Math.abs(E - drawn)).toBeLessThan(1e-6 * (Math.abs(drawn) + 1))
  })

  it('facing-away port: the stub-to-route join bend is charged', () => {
    const b = new DiagramBuilder()
    const n0 = b.ref(b.root, 'A', relSig([TERM]))
    const n1 = b.ref(b.root, 'B', relSig([TERM]))
    b.wire(b.root, [
      { node: n0, port: { kind: 'arg' as const, index: 0 } },
      { node: n1, port: { kind: 'arg' as const, index: 0 } },
    ])
    const d = b.build()
    const e = mkEngine(d, [])
    const bodies = [...e.bodies.values()].filter((x) => x.kind === 'ref')
    const A = bodies[0]!, B = bodies[1]!
    A.pos = { x: -80, y: 0 }; B.pos = { x: 80, y: 0 }
    const angOf = (bd: typeof A): number => {
      const la = [...bd.localAnchor.values()][0]!
      return Math.atan2(la.y, la.x)
    }
    A.theta = Math.PI - angOf(A) // port faces AWAY from B
    B.theta = Math.PI - angOf(B) // toward A
    e.frame = null
    recomputeRegions(e)

    const drawn = drawnWireCost(e)
    const E = wireEnergy(e)
    expect(Math.abs(E - drawn)).toBeLessThan(1e-6 * (Math.abs(drawn) + 1))
  })
})

describe('envelope probe evaluator (frozen paths)', () => {
  it('frozen eval equals the exact energy at the captured base (real replay scenes)', async () => {
    const { wireEnergyCapture, frozenWireEnergy } = await import('../../src/view/relax')
    const { bootFixture } = await import('../app/boot-fixture')
    const { mkReplay } = await import('../../src/app/replay')
    const { resolveOverlaps } = await import('../../src/view/relax')
    const ctx = (await bootFixture()).ctx
    for (const [nm, at] of [['plusComm', 20], ['succShiftS', 48]] as const) {
      const r = mkReplay(nm, ctx)
      const e = mkEngine(r.diagramAt(at), r.boundaryAt(at))
      recomputeRegions(e)
      resolveOverlaps(e)
      const cap = wireEnergyCapture(e)
      const frozen = frozenWireEnergy(e, cap.edges)
      // wire part of cap.E is the same sum over the same points/functions
      expect(Math.abs(frozen - cap.E), `${nm}@${at}: frozen != exact at base`).toBeLessThan(1e-9 * (Math.abs(cap.E) + 1))
    }
  })

  it('probe slopes match the exact energy exactly on an unobstructed scene', async () => {
    const { wireEnergyCapture, frozenWireEnergy } = await import('../../src/view/relax')
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
    A.theta = -angOf(A)
    B.theta = Math.PI - angOf(B)
    e.frame = null
    recomputeRegions(e)
    const cap = wireEnergyCapture(e)
    const h = 0.02
    for (const [dx, dy] of [[h, 0], [0, h], [-h, 0], [0, -h]] as const) {
      const saved = { ...A.pos }
      A.pos = { x: A.pos.x + dx, y: A.pos.y + dy }
      recomputeRegions(e)
      const frozen = frozenWireEnergy(e, cap.edges)
      const exact = wireEnergy(e)
      expect(Math.abs(frozen - exact), `probe (${dx},${dy})`).toBeLessThan(1e-9 * (Math.abs(exact) + 1))
      A.pos = saved
      recomputeRegions(e)
    }
  })
})
