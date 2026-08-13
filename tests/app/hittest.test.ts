import { describe, expect, it } from 'vitest'
import { buildSelection } from '../../src/app/hit-selection'
import {
  pendingWireHitTest,
  wireManipulationHitTest,
} from '../../src/app/hittest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkEngine, computeLegs } from '../../src/view'
import { vec } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

const viewport = { scale: 1 }

describe('hit selection policy', () => {
  it('anchors structural hits in one direct region', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    expect(buildSelection(diagram, [
      { kind: 'node', id: node },
      { kind: 'region', id: cut },
    ])).toMatchObject({
      region: diagram.root,
      nodes: [node],
      regions: [cut],
    })
  })

  it('rejects cross-region reaches', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const inner = builder.ref(cut, 'UnaryWitness', UNARY)
    const outer = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    expect(() => buildSelection(diagram, [
      { kind: 'node', id: inner },
      { kind: 'node', id: outer },
    ])).toThrow(/spans several regions/)
  })
})

describe('connection hit grammar', () => {
  it('distinguishes concrete endpoints — pins included — from wire bodies', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const a = builder.ref(cut, 'A', UNARY)
    const b = builder.ref(cut, 'B', UNARY)
    const c = builder.ref(cut, 'C', UNARY)
    const loose = builder.wire([{
      node: a,
      port: { kind: 'arg', index: 0 },
    }])
    // Every wire end is a node now: the free tip of `loose` is this pin, and
    // the pointer names it exactly as it names any other port terminal.
    const loosePin = builder.pin(loose, cut)
    const via = builder.wire([
      { node: b, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
    ])
    const engine = mkEngine(builder.build(), [])
    engine.bodies.get(a)!.pos = vec(-30, 0)
    engine.bodies.get(b)!.pos = vec(30, 0)
    engine.bodies.get(c)!.pos = vec(120, 0)
    engine.bodies.get(loosePin)!.pos = vec(-30, 40)
    engine.regions.set(cut, { center: vec(0, 0), radius: 55, support: [] })

    const endpointLeg = computeLegs(engine).find(({ leg }) =>
      leg.wid === loose && (leg.from.body === a || leg.to.body === a))!
    const endpointPoint = endpointLeg.leg.from.body === a
      ? endpointLeg.pts[0]!
      : endpointLeg.pts.at(-1)!
    expect(wireManipulationHitTest(engine, endpointPoint, viewport))
      .toMatchObject({
        kind: 'endpoint',
        wire: loose,
        endpoint: { node: a, port: { kind: 'arg', index: 0 } },
      })
    const pinPoint = endpointLeg.leg.from.body === a
      ? endpointLeg.pts.at(-1)!
      : endpointLeg.pts[0]!
    expect(wireManipulationHitTest(engine, pinPoint, viewport))
      .toMatchObject({
        kind: 'endpoint',
        wire: loose,
        endpoint: { node: loosePin, port: { kind: 'identity', index: 0 } },
      })
    const middle = endpointLeg.pts[Math.floor(endpointLeg.pts.length / 2)]!
    expect(wireManipulationHitTest(engine, middle, viewport))
      .toMatchObject({ kind: 'wireBody', wire: loose })

    const viaLeg = computeLegs(engine).find(({ leg }) => leg.wid === via)!
    const viaMiddle = viaLeg.pts[Math.floor(viaLeg.pts.length / 2)]!
    expect(wireManipulationHitTest(engine, viaMiddle, viewport))
      .toMatchObject({ kind: 'wireBody', wire: via })

    const pending = {
      wire: loose,
      bodyPaths: [[vec(-10, -20), vec(10, -20)]],
      looseEnd: vec(30, -20),
    }
    expect(pendingWireHitTest(pending, vec(0, -20), viewport)).toEqual({
      kind: 'pendingWireBody',
      wire: loose,
    })
    expect(pendingWireHitTest(pending, vec(30, -20), viewport)).toEqual({
      kind: 'pendingLooseEnd',
      wire: loose,
    })
  })
})
