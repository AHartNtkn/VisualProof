import { describe, expect, it } from 'vitest'
import { joinWires } from '../../src/app/edit'
import {
  ConnectionDragController,
  prepareMembraneContent,
  type ConnectionGesture,
} from '../../src/app/interact/connection'
import {
  membraneCrossingHits,
  preparedMembrane,
  type PreparedMembrane,
} from '../../src/app/hittest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram, NodeId, WireId } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import { applyDoubleCutIntro } from '../../src/kernel/rules/doublecut'
import { applyStep } from '../../src/kernel/proof/step'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import type { PointerSample } from '../../src/app/interact/viewport'
import { UNARY } from '../fixtures/zero-signature'

function sample(point: Vec2): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: point,
    screen: point,
    world: point,
    hit: null,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

function wrapNode(diagram: Diagram, node: NodeId): {
  readonly diagram: Diagram
  readonly membrane: PreparedMembrane
} {
  const wrapped = applyDoubleCutIntro(diagram, mkSelection(diagram, {
    region: diagram.nodes[node]!.region,
    regions: [],
    nodes: [node],
    wires: [],
  }))
  const inner = wrapped.nodes[node]!.region
  const outer = wrapped.regions[inner]!.kind === 'cut'
    ? wrapped.regions[inner]!.parent
    : ''
  return { diagram: wrapped, membrane: preparedMembrane(wrapped, outer)! }
}

function placeMembrane(
  engine: Engine,
  membrane: PreparedMembrane,
  center: Vec2,
): void {
  engine.regions.set(membrane.outer, {
    center,
    radius: 30,
    support: [],
  })
  engine.regions.set(membrane.inner, {
    center,
    radius: 18,
    support: [],
  })
  for (const node of membrane.selection.nodes) engine.bodies.get(node)!.pos = center
}

function membranePoint(engine: Engine, membrane: PreparedMembrane): Vec2 {
  const circle = engine.regions.get(membrane.outer)!
  return vec(circle.center.x, circle.center.y - circle.radius)
}

function crossingPoint(
  engine: Engine,
  membrane: PreparedMembrane,
  wire: WireId,
): Vec2 {
  return membraneCrossingHits(engine).find((hit) =>
    hit.key.membrane === membrane.outer && hit.key.wire === wire)!.at
}

function controller(
  engine: Engine,
  gestures: ConnectionGesture[],
  refusals: string[] = [],
): ConnectionDragController {
  return new ConnectionDragController({
    active: () => true,
    engine: () => engine,
    viewScale: () => 1,
    theme: () => LIGHT,
    relationGestures: true,
    commit: (gesture) => {
      gestures.push(gesture)
      return true
    },
    refuse: (text) => { refusals.push(text) },
  })
}

describe('structural connection commit', () => {
  it('identifies two homogeneous wires without term interpretation', () => {
    const builder = new DiagramBuilder()
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const joined = joinWires(builder.build(), [right, left])
    expect(Object.keys(joined.wires)).toEqual([left])
  })

  it('keeps the existing physical wire-to-wire drag as one wire gesture', () => {
    const builder = new DiagramBuilder()
    const left = builder.wire(builder.root, [])
    const right = builder.wire(builder.root, [])
    const engine = mkEngine(builder.build(), [])
    engine.bodies.get(`j:${left}`)!.pos = vec(-30, 0)
    engine.bodies.get(`j:${right}`)!.pos = vec(30, 0)
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, gestures)
    const claim = drag.claim(sample(vec(-30, 0)))!
    claim.move(sample(vec(30, 0)))
    claim.release(sample(vec(30, 0)), true)
    expect(gestures).toEqual([{
      kind: 'wire',
      source: { wire: left, endpoint: null },
      target: { wire: right, endpoint: null },
    }])
  })
})

describe('prepared membrane extraction', () => {
  it('puts tapped crossings first in tap order and leaves untapped crossings as parameters', () => {
    const builder = new DiagramBuilder()
    const ternary = relSig([IOTA, IOTA, IOTA])
    const content = builder.ref(builder.root, 'Triple', ternary)
    const first = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 0 },
    }])
    const second = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 1 },
    }])
    const parameter = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 2 },
    }])
    const wrapped = wrapNode(builder.build(), content)
    const prepared = prepareMembraneContent(wrapped.diagram, wrapped.membrane, [
      { membrane: wrapped.membrane.outer, wire: second },
      { membrane: wrapped.membrane.outer, wire: first },
    ])
    const extracted = extractSubgraph(wrapped.diagram, wrapped.membrane.selection)
    const stub = (wire: WireId): WireId =>
      extracted.pattern.boundary[extracted.attachments.indexOf(wire)]!

    expect(prepared.occurrence.args).toEqual([second, first])
    expect(prepared.content.boundary).toEqual([
      stub(second),
      stub(first),
      stub(parameter),
    ])
    expect(prepared.parameters).toEqual([parameter])
  })

  it('keeps a nullary tap prefix empty and emits every crossing as a parameter', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'Unary', UNARY)
    const parameter = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 0 },
    }])
    const wrapped = wrapNode(builder.build(), content)
    const prepared = prepareMembraneContent(wrapped.diagram, wrapped.membrane, [])
    expect(prepared.occurrence.args).toEqual([])
    expect(prepared.parameters).toEqual([parameter])
    expect(prepared.content.boundary).toHaveLength(1)
  })
})

describe('relation wire gestures', () => {
  it('grounds an existing relation wire through one membrane drop using only that membrane taps', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, UNARY)
    const content = builder.ref(negative, 'UnaryBody', UNARY)
    const formal = builder.wire(negative, [
      { node: application, port: { kind: 'arg', index: 0 } },
      { node: content, port: { kind: 'arg', index: 0 } },
    ])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], UNARY)
    const wrapped = wrapNode(builder.build(), content)
    const engine = mkEngine(wrapped.diagram, [])
    placeMembrane(engine, wrapped.membrane, vec(0, 0))
    engine.bodies.get(application)!.pos = vec(-70, 0)
    engine.bodies.get(`j:${relation}`)!.pos = vec(-90, 0)
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, gestures)

    const tap = drag.claim(sample(crossingPoint(engine, wrapped.membrane, formal)))!
    tap.release(sample(crossingPoint(engine, wrapped.membrane, formal)), false)
    const source = engine.bodies.get(`j:${relation}`)!.pos
    const claim = drag.claim(sample(source))!
    const target = membranePoint(engine, wrapped.membrane)
    claim.move(sample(target))
    claim.release(sample(target), true)

    expect(gestures).toHaveLength(1)
    expect(gestures[0]).toMatchObject({
      kind: 'relationJoin',
      input: {
        kind: 'relation',
        wire: relation,
        parameters: [],
      },
    })
    expect(gestures[0]!.kind === 'relationJoin'
      ? gestures[0]!.input.content.boundary
      : []).toHaveLength(1)
  })

  it('sends an invalid grounding drop to the kernel and preserves its refusal', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const application = builder.atom(negative, UNARY)
    const content = builder.ref(negative, 'UnaryBody', UNARY)
    builder.wire(negative, [
      { node: application, port: { kind: 'arg', index: 0 } },
      { node: content, port: { kind: 'arg', index: 0 } },
    ])
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], UNARY)
    const wrapped = wrapNode(builder.build(), content)
    const engine = mkEngine(wrapped.diagram, [])
    placeMembrane(engine, wrapped.membrane, vec(0, 0))
    engine.bodies.get(application)!.pos = vec(-70, 0)
    engine.bodies.get(`j:${relation}`)!.pos = vec(-90, 0)
    const refusals: string[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      relationGestures: true,
      commit: (gesture) => {
        if (gesture.kind !== 'relationJoin') return false
        try {
          applyStep(
            wrapped.diagram,
            { rule: 'wireJoin', input: gesture.input },
            EMPTY_PROOF_CONTEXT,
            'forward',
          )
          return true
        } catch (error) {
          refusals.push(error instanceof Error ? error.message : String(error))
          return false
        }
      },
      refuse: (text) => { refusals.push(text) },
    })

    const source = engine.bodies.get(`j:${relation}`)!.pos
    const claim = drag.claim(sample(source))!
    const target = membranePoint(engine, wrapped.membrane)
    claim.move(sample(target))
    claim.release(sample(target), true)

    expect(refusals).toEqual([
      'relation grounding boundary suffix has 0 positions; parameter count is 1',
    ])
    expect(drag.pendingState).toBeNull()
  })

  it('records endpoint contact, wire-body branches, and loose-end scope before one sever commit', () => {
    const builder = new DiagramBuilder()
    const nodes = [
      builder.ref(builder.root, 'UnaryBody', UNARY),
      builder.ref(builder.root, 'UnaryBody', UNARY),
      builder.ref(builder.root, 'UnaryBody', UNARY),
    ]
    const formals = nodes.map((node) => builder.wire(builder.root, [{
      node,
      port: { kind: 'arg', index: 0 },
    }]))
    let diagram = builder.build()
    const membranes: PreparedMembrane[] = []
    for (const node of nodes) {
      const wrapped = wrapNode(diagram, node)
      diagram = wrapped.diagram
      membranes.push(preparedMembrane(diagram, wrapped.membrane.outer)!)
    }
    const engine = mkEngine(diagram, [])
    const centers = [vec(-80, 0), vec(0, 0), vec(80, 0)]
    membranes.forEach((membrane, index) =>
      placeMembrane(engine, membrane, centers[index]!))
    formals.forEach((wire, index) => {
      engine.bodies.get(`j:${wire}`)!.pos = vec(centers[index]!.x, 70)
    })
    const gestures: ConnectionGesture[] = []
    const refusals: string[] = []
    const drag = controller(engine, gestures, refusals)
    for (let index = 0; index < 2; index++) {
      const point = crossingPoint(engine, membranes[index]!, formals[index]!)
      const tap = drag.claim(sample(point))!
      tap.release(sample(point), false)
    }

    const first = drag.claim(sample(membranePoint(engine, membranes[0]!)))!
    const secondPoint = membranePoint(engine, membranes[1]!)
    first.move(sample(secondPoint))
    first.release(sample(secondPoint), true)
    expect(drag.pendingState).not.toBeNull()
    expect(Object.keys(drag.pendingState!.diagram.wires)).toHaveLength(
      Object.keys(diagram.wires).length + 1,
    )
    expect(drag.pendingState!.engine.d).toBe(drag.pendingState!.diagram)
    expect(drag.pendingState!.engine.bodies.get(
      drag.pendingState!.looseEndBody,
    )!.pos).toBe(drag.pendingState!.looseEnd)

    const lateCrossing = crossingPoint(engine, membranes[0]!, formals[0]!)
    const lateTap = drag.claim(sample(lateCrossing))!
    lateTap.release(sample(lateCrossing), false)
    expect(refusals).toEqual([
      'tap formal crossings before the membrane contact',
    ])
    expect(drag.pendingState!.occurrences[0]!.args).toEqual([formals[0]])

    const thirdCrossing = crossingPoint(engine, membranes[2]!, formals[2]!)
    const thirdTap = drag.claim(sample(thirdCrossing))!
    thirdTap.release(sample(thirdCrossing), false)
    const branch = drag.claim(sample(drag.pendingState!.bodyPoint))!
    const thirdPoint = membranePoint(engine, membranes[2]!)
    branch.move(sample(thirdPoint))
    branch.release(sample(thirdPoint), true)
    expect(drag.pendingState!.occurrences).toHaveLength(3)

    const loose = drag.claim(sample(drag.pendingState!.looseEnd))!
    const scopePoint = vec(0, 100)
    loose.move(sample(scopePoint))
    loose.release(sample(scopePoint), true)

    expect(gestures).toHaveLength(1)
    expect(gestures[0]).toEqual({
      kind: 'relationSever',
      input: {
        kind: 'relation',
        scope: diagram.root,
        occurrences: membranes.map((membrane, index) => ({
          sel: membrane.selection,
          args: [formals[index]!],
        })),
      },
    })
    expect(drag.pendingState).toBeNull()
  })

  it('routes kernel refusal through spring-back and cancel deletes a pending legal wire', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'UnaryBody', UNARY)
    const formal = builder.wire(builder.root, [{
      node: content,
      port: { kind: 'arg', index: 0 },
    }])
    const wrapped = wrapNode(builder.build(), content)
    const engine = mkEngine(wrapped.diagram, [])
    placeMembrane(engine, wrapped.membrane, vec(0, 0))
    engine.bodies.get(`j:${formal}`)!.pos = vec(0, 70)
    const refusals: string[] = []
    const scopeAtCommit: string[] = []
    const bodyHomeAtCommit: string[] = []
    let drag!: ConnectionDragController
    drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      relationGestures: true,
      commit: (gesture) => {
        if (gesture.kind === 'relationSever') {
          const pending = drag.pendingState!
          scopeAtCommit.push(pending.diagram.wires[pending.wire]!.scope)
          bodyHomeAtCommit.push(
            pending.engine.bodies.get(pending.looseEndBody)!.region,
          )
        }
        try {
          const step = gesture.kind === 'relationSever'
            ? { rule: 'wireSever' as const, input: gesture.input }
            : gesture.kind === 'relationJoin'
              ? { rule: 'wireJoin' as const, input: gesture.input }
              : {
                  rule: 'wireJoin' as const,
                  input: {
                    kind: 'iota' as const,
                    a: gesture.source.wire,
                    b: gesture.target.wire,
                  },
                }
          applyStep(wrapped.diagram, step, EMPTY_PROOF_CONTEXT, 'backward')
          return true
        } catch (error) {
          refusals.push(error instanceof Error ? error.message : String(error))
          return false
        }
      },
      refuse: (text) => { refusals.push(text) },
    })
    const tapPoint = crossingPoint(engine, wrapped.membrane, formal)
    const tap = drag.claim(sample(tapPoint))!
    tap.release(sample(tapPoint), false)
    const found = drag.claim(sample(membranePoint(engine, wrapped.membrane)))!
    found.release(sample(membranePoint(engine, wrapped.membrane)), false)
    const loose = drag.claim(sample(drag.pendingState!.looseEnd))!
    const finish = vec(10, 10)
    loose.move(sample(finish))
    loose.release(sample(finish), true)
    expect(refusals.join('\n')).toMatch(/requires a negative scope/)
    expect(scopeAtCommit).toEqual([wrapped.membrane.inner])
    expect(bodyHomeAtCommit).toEqual([wrapped.membrane.inner])
    expect(drag.pendingState).toBeNull()

    const again = drag.claim(sample(membranePoint(engine, wrapped.membrane)))!
    again.release(sample(membranePoint(engine, wrapped.membrane)), false)
    expect(drag.pendingState).not.toBeNull()
    expect(drag.pendingState!.occurrences).toHaveLength(1)
    expect(drag.pendingState!.occurrences[0]!.args).toEqual([formal])
    drag.cancel()
    expect(drag.pendingState).toBeNull()
  })

  it('lets the kernel refuse explicitly touched occurrences that are not copies', () => {
    const builder = new DiagramBuilder()
    const firstNode = builder.ref(builder.root, 'FirstBody', UNARY)
    const secondNode = builder.ref(builder.root, 'DifferentBody', UNARY)
    const firstFormal = builder.wire(builder.root, [{
      node: firstNode,
      port: { kind: 'arg', index: 0 },
    }])
    const secondFormal = builder.wire(builder.root, [{
      node: secondNode,
      port: { kind: 'arg', index: 0 },
    }])
    let diagram = builder.build()
    const firstWrapped = wrapNode(diagram, firstNode)
    diagram = firstWrapped.diagram
    const secondWrapped = wrapNode(diagram, secondNode)
    diagram = secondWrapped.diagram
    const first = preparedMembrane(diagram, firstWrapped.membrane.outer)!
    const second = preparedMembrane(diagram, secondWrapped.membrane.outer)!
    const engine = mkEngine(diagram, [])
    placeMembrane(engine, first, vec(-50, 0))
    placeMembrane(engine, second, vec(50, 0))
    engine.bodies.get(`j:${firstFormal}`)!.pos = vec(-50, 70)
    engine.bodies.get(`j:${secondFormal}`)!.pos = vec(50, 70)
    const refusals: string[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      relationGestures: true,
      commit: (gesture) => {
        if (gesture.kind !== 'relationSever') return false
        try {
          applyStep(
            diagram,
            { rule: 'wireSever', input: gesture.input },
            EMPTY_PROOF_CONTEXT,
            'forward',
          )
          return true
        } catch (error) {
          refusals.push(error instanceof Error ? error.message : String(error))
          return false
        }
      },
      refuse: (text) => { refusals.push(text) },
    })
    for (const [membrane, wire] of [
      [first, firstFormal],
      [second, secondFormal],
    ] as const) {
      const point = crossingPoint(engine, membrane, wire)
      const tap = drag.claim(sample(point))!
      tap.release(sample(point), false)
    }
    const found = drag.claim(sample(membranePoint(engine, first)))!
    const secondPoint = membranePoint(engine, second)
    found.move(sample(secondPoint))
    found.release(sample(secondPoint), true)
    const loose = drag.claim(sample(drag.pendingState!.looseEnd))!
    const scope = vec(0, 100)
    loose.move(sample(scope))
    loose.release(sample(scope), true)

    expect(refusals).toEqual([
      'occurrences are not isomorphic under the same pinned content',
    ])
    expect(drag.pendingState).toBeNull()
  })
})
