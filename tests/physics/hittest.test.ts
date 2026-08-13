import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, recomputeRegions, legPaths, settle, computeLegs } from '../../src/view/index'
import { hitTest, dragTarget } from '../../src/app/hittest'
import { unaryDefinition, UNARY } from '../fixtures/zero-signature'

const viewport = (scale = 1) => ({ scale })

describe('settled hit targets', () => {
  // A pin is an ordinary identity NODE (dots are ordinary nodes, USER
  // 2026-07-24): its disc hit-tests as that node, for clicks and drags alike —
  // the wire is reachable from the node, never guessed for it.
  it('a point on a pin disc resolves to the pin node (clicks and drags alike)', () => {
    const h = new DiagramBuilder()
    const a = h.ref(h.root, 'Unary', UNARY)
    const w = h.wire([{ node: a, port: { kind: 'arg', index: 0 } }])
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
    // the pin is the identity body build() attached to the singleton wire
    const j = e.bodies.get(e.wires.get(w)!.binds.find((bind) =>
      e.bodies.get(bind.body)!.kind === 'identity')!.body)!
    expect(hitTest(e, j.pos, viewport())).toEqual({ kind: 'node', id: j.id })
    expect(dragTarget(e, j.pos, viewport())).toEqual({ kind: 'carrier', id: j.id })
  })

  it('a click on a branch junction resolves to its wire — hit-tested on the DRAWN tributary curves', () => {
    const h = new DiagramBuilder()
    const a = h.ref(h.root, 'A', UNARY)
    const b = h.ref(h.root, 'B', UNARY)
    const c = h.ref(h.root, 'C', UNARY)
    const w = h.wire([
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: b, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
    ])
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
    recomputeRegions(e)
    const legs = legPaths(e).filter((l) => l.wid === w)
    expect(legs.length, 'the junction is drawn as its legs').toBeGreaterThan(0)
    const curve = legs.map((l) => l.pts).find((pl) => pl.length > 2)!
    const mid = curve[Math.floor(curve.length / 2)]!
    expect(hitTest(e, mid, viewport())).toEqual({ kind: 'wire', id: w })
  })

  it('a click on a boundary wire (its leg near the frame slot) resolves to that wire', () => {
    const nat = unaryDefinition()
    const e = mkEngine(nat.diagram, nat.boundary)
    settle(e, 1200)
    const wid = nat.boundary[0]!
    const leg = computeLegs(e).find((g) => g.leg.wid === wid)!
    expect(leg).toBeDefined()
    const pt = leg.pts[Math.floor(leg.pts.length * 0.75)]!
    expect(hitTest(e, pt, viewport())).toEqual({ kind: 'wire', id: wid })
  })
})
