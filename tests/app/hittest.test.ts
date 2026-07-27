import { describe, expect, it } from 'vitest'
import { buildSelection } from '../../src/app/hit-selection'
import {
  connectionHitTest,
  membraneCrossingHits,
  pendingWireHitTest,
  preparedMembrane,
  wireManipulationHitTest,
} from '../../src/app/hittest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkEngine, computeLegs } from '../../src/view'
import { vec } from '../../src/view/vec'
import { BINARY, UNARY } from '../fixtures/zero-signature'

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

describe('relation membrane hit grammar', () => {
  it('recognizes only an erasable outer double-cut and selects its exact inner content', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'Pair', BINARY)
    const diagram = builder.build()
    const wrapped = applyDoubleCutIntro(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [content],
      wires: [],
    }))
    const inner = wrapped.nodes[content]!.region
    const outer = wrapped.regions[inner]!.kind === 'cut'
      ? wrapped.regions[inner]!.parent
      : ''
    expect(preparedMembrane(wrapped, outer)).toMatchObject({
      outer,
      inner,
      selection: {
        region: inner,
        regions: [],
        nodes: [content],
      },
    })
    expect(preparedMembrane(wrapped, inner)).toBeNull()
  })

  it('includes every direct inner item and rejects dirty annuli', () => {
    const exact = new DiagramBuilder()
    const outer = exact.cut(exact.root)
    const inner = exact.cut(outer)
    const child = exact.cut(inner)
    const node = exact.ref(inner, 'Content', relSig([]))
    exact.ref(child, 'Nested', relSig([]))
    const wire = exact.relWire(inner, relSig([]))
    const diagram = exact.build()
    expect(preparedMembrane(diagram, outer)).toEqual({
      outer,
      inner,
      selection: mkSelection(diagram, {
        region: inner,
        regions: [child],
        nodes: [node],
        wires: [wire],
      }),
    })

    const dirty = new DiagramBuilder()
    const withNode = dirty.cut(dirty.root)
    dirty.cut(withNode)
    dirty.ref(withNode, 'AnnulusNode', relSig([]))
    const withWire = dirty.cut(dirty.root)
    dirty.cut(withWire)
    dirty.relWire(withWire, relSig([]))
    const withChildren = dirty.cut(dirty.root)
    dirty.cut(withChildren)
    dirty.cut(withChildren)
    const dirtyDiagram = dirty.build()
    expect(preparedMembrane(dirtyDiagram, withNode)).toBeNull()
    expect(preparedMembrane(dirtyDiagram, withWire)).toBeNull()
    expect(preparedMembrane(dirtyDiagram, withChildren)).toBeNull()
  })

  it('exposes a stable membrane-and-wire crossing ahead of the ordinary wire body', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'Unary', UNARY)
    const crossing = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 0 },
    }], IOTA)
    const diagram = builder.build()
    const wrapped = applyDoubleCutIntro(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [content],
      wires: [],
    }))
    const inner = wrapped.nodes[content]!.region
    const outer = wrapped.regions[inner]!.kind === 'cut'
      ? wrapped.regions[inner]!.parent
      : ''
    const engine = mkEngine(wrapped, [])
    engine.bodies.get(content)!.pos = vec(0, 0)
    engine.bodies.get(`j:${crossing}`)!.pos = vec(80, 0)
    engine.regions.set(inner, { center: vec(0, 0), radius: 18, support: [] })
    engine.regions.set(outer, { center: vec(0, 0), radius: 30, support: [] })

    const hit = membraneCrossingHits(engine).find((candidate) =>
      candidate.key.membrane === outer && candidate.key.wire === crossing)
    expect(hit).toBeDefined()
    expect(connectionHitTest(engine, hit!.at, viewport)).toEqual(hit)

    engine.bodies.get(`j:${crossing}`)!.pos = vec(80, 12)
    const moved = membraneCrossingHits(engine).find((candidate) =>
      candidate.key.membrane === outer && candidate.key.wire === crossing)
    expect(moved?.key).toEqual(hit?.key)
    expect(moved?.at).not.toEqual(hit?.at)

    expect(connectionHitTest(engine, vec(0, 30), viewport)).toMatchObject({
      kind: 'membrane',
      membrane: { outer, inner },
    })
    expect(connectionHitTest(engine, vec(0, 10), viewport)).toEqual({
      kind: 'region',
      region: inner,
    })
  })

  it('distinguishes concrete endpoints, loose ends, vias, and wire bodies', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const a = builder.ref(cut, 'A', UNARY)
    const b = builder.ref(cut, 'B', UNARY)
    const c = builder.ref(cut, 'C', UNARY)
    const loose = builder.wire(cut, [{
      node: a,
      port: { kind: 'arg', index: 0 },
    }])
    const via = builder.wire(builder.root, [
      { node: b, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
    ])
    const engine = mkEngine(builder.build(), [])
    engine.bodies.get(a)!.pos = vec(-30, 0)
    engine.bodies.get(b)!.pos = vec(30, 0)
    engine.bodies.get(c)!.pos = vec(45, 0)
    engine.bodies.get(`j:${loose}`)!.pos = vec(-30, 40)
    engine.bodies.get(`x:${via}`)!.pos = vec(30, 40)
    engine.regions.set(cut, { center: vec(0, 0), radius: 55, support: [] })

    expect(wireManipulationHitTest(
      engine,
      engine.bodies.get(`j:${loose}`)!.pos,
      viewport,
    )).toMatchObject({ kind: 'looseEnd', wire: loose })
    expect(wireManipulationHitTest(
      engine,
      engine.bodies.get(`x:${via}`)!.pos,
      viewport,
    )).toMatchObject({ kind: 'via', wire: via })
    const endpointLeg = computeLegs(engine).find(({ leg }) =>
      leg.wid === loose && (leg.from.body === a || leg.to.body === a))!
    const endpointPoint = endpointLeg.leg.from.body === a
      ? endpointLeg.pts[0]!
      : endpointLeg.pts.at(-1)!
    expect(wireManipulationHitTest(engine, endpointPoint, viewport))
      .toMatchObject({ kind: 'endpoint', wire: loose })
    const middle = endpointLeg.pts[Math.floor(endpointLeg.pts.length / 2)]!
    expect(wireManipulationHitTest(engine, middle, viewport))
      .toMatchObject({ kind: 'wireBody', wire: loose })
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
