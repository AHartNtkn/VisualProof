import { describe, expect, it } from 'vitest'
import type { Hit } from '../../src/app/hittest'
import {
  ConnectionDragController,
  prepareSelectedOccurrence,
  type ConnectionGesture,
  type PendingRelationState,
} from '../../src/app/interact/connection'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { NodeId, WireId } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../src/kernel/diagram/subgraph/extract'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { applyStep } from '../../src/kernel/proof/step'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

type SelectionState = { hits: readonly Hit[] }

function sample(point: Vec2, hit: Hit | null = null): PointerSample {
  return {
    pointerId: 1,
    button: 0,
    client: point,
    screen: point,
    world: point,
    hit,
    shiftKey: false,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
  }
}

function nodeHit(id: NodeId): Hit {
  return { kind: 'node', id }
}

function wireHit(id: WireId): Hit {
  return { kind: 'wire', id }
}

function controller(
  engine: Engine,
  selection: SelectionState,
  gestures: ConnectionGesture[],
  refusals: string[] = [],
  commit?: (gesture: ConnectionGesture) => boolean,
): ConnectionDragController {
  return new ConnectionDragController({
    active: () => true,
    engine: () => engine,
    viewScale: () => 1,
    theme: () => LIGHT,
    relationSelection: {
      selection: () => selection.hits,
      setSelection: (hits) => { selection.hits = hits },
    },
    commit: (gesture) => {
      gestures.push(gesture)
      return commit?.(gesture) ?? true
    },
    refuse: (text) => { refusals.push(text) },
  })
}

function pendingLooseEnd(pending: PendingRelationState): Vec2 {
  return pending.engine.bodies.get(pending.looseEndBody)!.pos
}

function pendingBodyPoint(
  drag: ConnectionDragController,
  pending: PendingRelationState,
): Vec2 {
  const loose = pendingLooseEnd(pending)
  return drag.overlay()
    .filter((shape) => shape.kind === 'circle')
    .map((shape) => shape.center)
    .find((point) => point.x !== loose.x || point.y !== loose.y)!
}

describe('ordered selected occurrence projection', () => {
  it('uses region/node hits for extent and relative wire-hit order for formals', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(
      builder.root,
      'TernaryBody',
      relSig([IOTA, IOTA, IOTA]),
    )
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
    const diagram = builder.build()
    const prepared = prepareSelectedOccurrence(diagram, [
      wireHit(second),
      nodeHit(content),
      wireHit(first),
    ])
    const extracted = extractSubgraph(diagram, prepared.occurrence.sel)
    const stub = (wire: WireId): WireId =>
      extracted.pattern.boundary[extracted.attachments.indexOf(wire)]!

    expect(prepared.occurrence).toEqual({
      sel: expect.objectContaining({
        region: diagram.root,
        regions: [],
        nodes: [content],
        wires: [],
      }),
      args: [second, first],
    })
    expect(prepared.content.boundary).toEqual([
      stub(second),
      stub(first),
      stub(parameter),
    ])
    expect(prepared.parameters).toEqual([parameter])
  })

  it('supports nullary selection and rejects a formal outside the selected extent', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'TruthBody', relSig([]))
    const outside = builder.wire(builder.root, [])
    const diagram = builder.build()

    expect(prepareSelectedOccurrence(diagram, [nodeHit(content)]))
      .toMatchObject({
        occurrence: { args: [] },
        content: { boundary: [] },
        parameters: [],
      })
    expect(() => prepareSelectedOccurrence(diagram, [
      nodeHit(content),
      wireHit(outside),
    ])).toThrowError(/selected formal wire .* does not cross the selected extent/)
  })
})

describe('relation wire gestures from one ordered selection', () => {
  it('keeps ordinary iota wire-to-wire dragging unchanged', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [])
    const right = builder.wire(negative, [])
    const engine = mkEngine(builder.build(), [])
    const leftPoint = engine.bodies.get(`j:${left}`)!.pos
    const rightPoint = engine.bodies.get(`j:${right}`)!.pos
    const gestures: ConnectionGesture[] = []
    const drag = new ConnectionDragController({
      active: () => true,
      engine: () => engine,
      viewScale: () => 1,
      theme: () => LIGHT,
      commit: (gesture) => { gestures.push(gesture); return true },
      refuse: () => undefined,
    })

    const claim = drag.claim(sample(leftPoint, wireHit(left)))!
    claim.move(sample(rightPoint, wireHit(right)))
    claim.release(sample(rightPoint, wireHit(right)), true)

    expect(gestures).toEqual([{
      kind: 'wire',
      source: { wire: left, endpoint: null },
      target: { wire: right, endpoint: null },
    }])
  })

  it('grounds onto a physically hit selected extent and consumes selection on success', () => {
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
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(application)!.pos = vec(-70, 0)
    engine.bodies.get(content)!.pos = vec(30, 0)
    engine.bodies.get(`j:${relation}`)!.pos = vec(-100, 0)
    const selection: SelectionState = {
      hits: [wireHit(formal), nodeHit(content)],
    }
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, selection, gestures)
    const source = engine.bodies.get(`j:${relation}`)!.pos
    const target = engine.bodies.get(content)!.pos

    const claim = drag.claim(sample(source, wireHit(relation)))!
    claim.move(sample(target, nodeHit(content)))
    claim.release(sample(target, nodeHit(content)), true)

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
    expect(selection.hits).toEqual([])
  })

  it('sends invalid grounding to the kernel and retains the prepared selection', () => {
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
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(application)!.pos = vec(-70, 0)
    engine.bodies.get(content)!.pos = vec(30, 0)
    engine.bodies.get(`j:${relation}`)!.pos = vec(-100, 0)
    const selection: SelectionState = { hits: [nodeHit(content)] }
    const refusals: string[] = []
    const gestures: ConnectionGesture[] = []
    const drag = controller(
      engine,
      selection,
      gestures,
      refusals,
      (gesture) => {
        if (gesture.kind !== 'relationJoin') return false
        try {
          applyStep(
            diagram,
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
    )
    const source = engine.bodies.get(`j:${relation}`)!.pos
    const target = engine.bodies.get(content)!.pos

    const claim = drag.claim(sample(source, wireHit(relation)))!
    claim.move(sample(target, nodeHit(content)))
    claim.release(sample(target, nodeHit(content)), true)

    expect(refusals).toEqual([
      'relation grounding boundary suffix has 0 positions; parameter count is 1',
    ])
    expect(selection.hits).toEqual([nodeHit(content)])
    expect(drag.pendingState).toBeNull()
  })

  it('refuses an invalid founding selection without creating pending state', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'TruthBody', relSig([]))
    const outside = builder.wire(builder.root, [])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(content)!.pos = vec(0, 0)
    const selection: SelectionState = {
      hits: [nodeHit(content), wireHit(outside)],
    }
    const refusals: string[] = []
    const drag = controller(engine, selection, [], refusals)

    expect(() => {
      const founding = drag.claim(sample(vec(0, 0), nodeHit(content)))!
      founding.move(sample(vec(0, 80)))
      founding.release(sample(vec(0, 80)), true)
    }).not.toThrow()
    expect(refusals).toEqual([
      `selected formal wire '${outside}' does not cross the selected extent`,
    ])
    expect(drag.pendingState).toBeNull()
    expect(selection.hits).toEqual([nodeHit(content), wireHit(outside)])
  })

  it('records one selected occurrence per founding/body drag and loose-end scope at commit', () => {
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
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const centers = [vec(-80, 0), vec(0, 0), vec(80, 0)]
    nodes.forEach((node, index) => {
      engine.bodies.get(node)!.pos = centers[index]!
      engine.bodies.get(`j:${formals[index]!}`)!.pos = vec(centers[index]!.x, 60)
    })
    const selection: SelectionState = {
      hits: [nodeHit(nodes[0]!), wireHit(formals[0]!)],
    }
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, selection, gestures)

    const founding = drag.claim(sample(centers[0]!, nodeHit(nodes[0]!)))!
    founding.move(sample(vec(-80, 80)))
    founding.release(sample(vec(-80, 80)), true)
    expect(selection.hits).toEqual([])
    expect(drag.pendingState?.occurrences).toHaveLength(1)

    for (let index = 1; index < nodes.length; index++) {
      selection.hits = [
        wireHit(formals[index]!),
        nodeHit(nodes[index]!),
      ]
      const body = pendingBodyPoint(drag, drag.pendingState!)
      const branch = drag.claim(sample(body))!
      branch.move(sample(centers[index]!, nodeHit(nodes[index]!)))
      branch.release(sample(centers[index]!, nodeHit(nodes[index]!)), true)
      expect(selection.hits).toEqual([])
    }

    const pending = drag.pendingState!
    const loosePoint = pendingLooseEnd(pending)
    const loose = drag.claim(sample(loosePoint))!
    const scopePoint = vec(0, 120)
    loose.move(sample(scopePoint))
    loose.release(sample(scopePoint), true)

    expect(gestures).toEqual([{
      kind: 'relationSever',
      input: {
        kind: 'relation',
        scope: diagram.root,
        occurrences: nodes.map((node, index) => ({
          sel: prepareSelectedOccurrence(diagram, [
            nodeHit(node),
            wireHit(formals[index]!),
          ]).occurrence.sel,
          args: [formals[index]!],
        })),
      },
    }])
    expect(drag.pendingState).toBeNull()
  })

  it('lets the kernel refuse mismatched explicit occurrences and springs the loose end back', () => {
    const builder = new DiagramBuilder()
    const first = builder.ref(builder.root, 'FirstBody', UNARY)
    const second = builder.ref(builder.root, 'DifferentBody', UNARY)
    const firstFormal = builder.wire(builder.root, [{
      node: first,
      port: { kind: 'arg', index: 0 },
    }])
    const secondFormal = builder.wire(builder.root, [{
      node: second,
      port: { kind: 'arg', index: 0 },
    }])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(first)!.pos = vec(-50, 0)
    engine.bodies.get(second)!.pos = vec(50, 0)
    const selection: SelectionState = {
      hits: [nodeHit(first), wireHit(firstFormal)],
    }
    const gestures: ConnectionGesture[] = []
    const refusals: string[] = []
    const drag = controller(
      engine,
      selection,
      gestures,
      refusals,
      (gesture) => {
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
    )
    const founding = drag.claim(sample(vec(-50, 0), nodeHit(first)))!
    founding.move(sample(vec(-50, 80)))
    founding.release(sample(vec(-50, 80)), true)
    selection.hits = [wireHit(secondFormal), nodeHit(second)]
    const branch = drag.claim(sample(pendingBodyPoint(drag, drag.pendingState!)))!
    branch.move(sample(vec(50, 0), nodeHit(second)))
    branch.release(sample(vec(50, 0), nodeHit(second)), true)
    const before = pendingLooseEnd(drag.pendingState!)
    const loose = drag.claim(sample(before))!
    loose.move(sample(vec(0, 120)))
    loose.release(sample(vec(0, 120)), true)

    expect(refusals).toEqual([
      'occurrences are not isomorphic under the same pinned content',
    ])
    expect(drag.pendingState).not.toBeNull()
    expect(pendingLooseEnd(drag.pendingState!)).toEqual(before)

    drag.cancel()
    expect(drag.pendingState).toBeNull()
  })

  it('derives contact geometry from the live selected node owner', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'TruthBody', relSig([]))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(content)!.pos = vec(-100, 0)
    const selection: SelectionState = { hits: [nodeHit(content)] }
    const drag = controller(engine, selection, [])
    const founding = drag.claim(sample(vec(-100, 0), nodeHit(content)))!
    founding.move(sample(vec(-100, 80)))
    founding.release(sample(vec(-100, 80)), true)
    const oldBody = pendingBodyPoint(drag, drag.pendingState!)

    engine.bodies.get(content)!.pos = vec(80, 50)
    const movedBody = pendingBodyPoint(drag, drag.pendingState!)

    expect(movedBody).not.toEqual(oldBody)
    expect(drag.claim(sample(oldBody))).toBeNull()
    expect(drag.claim(sample(movedBody))).not.toBeNull()
  })
})
