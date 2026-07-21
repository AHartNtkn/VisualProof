import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, recomputeRegions, legPaths, settle, computeLegs } from '../../src/view/index'
import { buildFregeTheory } from '../../src/theories/frege'
import { hitTest, dragTarget } from '../../src/interaction/hittest'

const p = (s: string) => parseTerm(s)
const viewport = (scale = 1) => ({ scale })

describe('settled hit targets', () => {
  it('a point on an ∃ dot grabs its homed body (clicks resolve it to the wire, drags do not)', () => {
    const h = new DiagramBuilder()
    const a = h.termNode(h.root, p('\\x. x'))
    const w = h.wire(h.root, [{ node: a, port: { kind: 'output' } }])
    const e = mkEngine(h.build(), [])
    settle(e, 2600)
    const j = e.bodies.get(e.wires.get(w)!.tipBodyId!)!
    expect(hitTest(e, j.pos, viewport())).toEqual({ kind: 'wire', id: w })
    expect(dragTarget(e, j.pos, viewport())).toEqual({ kind: 'body', id: j.id })
  })

  it('a click on a branch junction resolves to its wire — hit-tested on the DRAWN tributary curves', () => {
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
    recomputeRegions(e)
    const legs = legPaths(e).filter((l) => l.wid === w)
    expect(legs.length, 'the junction is drawn as its legs').toBeGreaterThan(0)
    const curve = legs.map((l) => l.pts).find((pl) => pl.length > 2)!
    const mid = curve[Math.floor(curve.length / 2)]!
    expect(hitTest(e, mid, viewport())).toEqual({ kind: 'wire', id: w })
  })

  it('a click on a boundary wire (its leg near the frame slot) resolves to that wire', () => {
    const nat = new Map(buildFregeTheory().relations).get('nat')!
    const e = mkEngine(nat.diagram, nat.boundary)
    settle(e, 1200)
    const wid = nat.boundary[0]!
    const leg = computeLegs(e).find((g) => g.leg.wid === wid)!
    expect(leg).toBeDefined()
    const pt = leg.pts[Math.floor(leg.pts.length * 0.75)]!
    expect(hitTest(e, pt, viewport())).toEqual({ kind: 'wire', id: wid })
  })
})
