import { describe, expect, it } from 'vitest'
import type { Hit } from '../../src/app/hittest'
import {
  ConnectionDragController,
  prepareSelectedOccurrences,
  type ConnectionGesture,
  type PendingRelationState,
} from '../../src/app/interact/connection'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { NodeId, RegionId, WireId } from '../../src/kernel/diagram/diagram'
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

function regionHit(id: RegionId): Hit {
  return { kind: 'region', id }
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

describe('structural occurrence projection from one ordered selection', () => {
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
    const [prepared] = prepareSelectedOccurrences(diagram, [
      wireHit(second),
      nodeHit(content),
      wireHit(first),
    ])
    if (prepared === undefined) throw new Error('expected one prepared occurrence')
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

  it('merges same-region extent and partitions across unhighlighted cuts', () => {
    const builder = new DiagramBuilder()
    const sameA = builder.ref(builder.root, 'SameA', relSig([]))
    const sameB = builder.ref(builder.root, 'SameB', relSig([]))
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const splitA = builder.ref(firstCut, 'Split', relSig([]))
    const splitB = builder.ref(secondCut, 'Split', relSig([]))
    const diagram = builder.build()

    const same = prepareSelectedOccurrences(diagram, [
      nodeHit(sameA),
      nodeHit(sameB),
    ])
    expect(same).toHaveLength(1)
    expect(same[0]!.occurrence.sel).toMatchObject({
      region: diagram.root,
      regions: [],
      nodes: [sameA, sameB],
    })

    const split = prepareSelectedOccurrences(diagram, [
      nodeHit(splitA),
      nodeHit(splitB),
    ])
    expect(split).toHaveLength(2)
    expect(split.map(({ occurrence }) => occurrence.sel.region)).toEqual([
      firstCut,
      secondCut,
    ])
  })

  it('merges across highlighted cut boundaries and keeps wire order global', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const outside = builder.ref(builder.root, 'Pair', UNARY)
    const inside = builder.ref(cut, 'Pair', UNARY)
    const outsideArg = builder.wire(builder.root, [{
      node: outside,
      port: { kind: 'arg', index: 0 },
    }])
    const insideArg = builder.wire(builder.root, [{
      node: inside,
      port: { kind: 'arg', index: 0 },
    }])
    const diagram = builder.build()

    const occurrences = prepareSelectedOccurrences(diagram, [
      wireHit(insideArg),
      nodeHit(outside),
      regionHit(cut),
      wireHit(outsideArg),
      nodeHit(inside),
    ])

    expect(occurrences).toHaveLength(1)
    expect(occurrences[0]!.occurrence).toMatchObject({
      sel: {
        region: diagram.root,
        regions: [cut],
        nodes: [outside],
        wires: [],
      },
      args: [insideArg, outsideArg],
    })
  })

  it('keeps extent beyond an unhighlighted nested cut in a separate occurrence', () => {
    const builder = new DiagramBuilder()
    const highlighted = builder.cut(builder.root)
    const unhighlighted = builder.cut(highlighted)
    const nested = builder.ref(unhighlighted, 'Nested', relSig([]))
    const diagram = builder.build()

    const occurrences = prepareSelectedOccurrences(diagram, [
      regionHit(highlighted),
      nodeHit(nested),
    ])

    expect(occurrences).toHaveLength(2)
    expect(occurrences.map(({ occurrence }) => occurrence.sel)).toEqual([
      expect.objectContaining({
        region: diagram.root,
        regions: [highlighted],
      }),
      expect.objectContaining({
        region: unhighlighted,
        nodes: [nested],
      }),
    ])
  })

  it('supports nullary selection and rejects a formal outside every selected occurrence', () => {
    const builder = new DiagramBuilder()
    const content = builder.ref(builder.root, 'TruthBody', relSig([]))
    const outside = builder.wire(builder.root, [])
    const diagram = builder.build()

    expect(prepareSelectedOccurrences(diagram, [nodeHit(content)]))
      .toMatchObject([{
        occurrence: { args: [] },
        content: { boundary: [] },
        parameters: [],
      }])
    expect(() => prepareSelectedOccurrences(diagram, [
      nodeHit(content),
      wireHit(outside),
    ])).toThrowError(/selected formal wire .* does not cross any selected occurrence/)
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

  it('grounds only the contacted structural occurrence and leaves the others highlighted', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const separated = builder.cut(negative)
    const application = builder.atom(negative, relSig([]))
    const content = builder.ref(negative, 'Grounded', relSig([]))
    const untouched = builder.ref(separated, 'Untouched', relSig([]))
    const relation = builder.wire(negative, [{
      node: application,
      port: { kind: 'head' },
    }], relSig([]))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(application)!.pos = vec(-70, 0)
    engine.bodies.get(content)!.pos = vec(30, 0)
    engine.bodies.get(untouched)!.pos = vec(100, 0)
    engine.bodies.get(`j:${relation}`)!.pos = vec(-100, 0)
    const selection: SelectionState = {
      hits: [nodeHit(untouched), nodeHit(content)],
    }
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, selection, gestures)
    const source = engine.bodies.get(`j:${relation}`)!.pos
    const target = engine.bodies.get(content)!.pos

    const claim = drag.claim(sample(source, wireHit(relation)))!
    claim.move(sample(target, nodeHit(content)))
    claim.release(sample(target, nodeHit(content)), true)

    expect(gestures).toHaveLength(1)
    expect(selection.hits).toEqual([nodeHit(untouched)])
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
      `selected formal wire '${outside}' does not cross any selected occurrence`,
    ])
    expect(drag.pendingState).toBeNull()
    expect(selection.hits).toEqual([nodeHit(content), wireHit(outside)])
  })

  it('contacts structurally parsed occurrences, leaves untouched highlights, and commits loose-end scope', () => {
    const builder = new DiagramBuilder()
    const regions = Array.from({ length: 4 }, () => builder.cut(builder.root))
    const nodes = regions.map((region) =>
      builder.ref(region, 'UnaryBody', UNARY))
    const formals = nodes.map((node, index) => builder.wire(regions[index]!, [{
      node,
      port: { kind: 'arg', index: 0 },
    }]))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const centers = [vec(-120, 0), vec(-40, 0), vec(40, 0), vec(120, 0)]
    nodes.forEach((node, index) => {
      engine.bodies.get(node)!.pos = centers[index]!
      engine.bodies.get(`j:${formals[index]!}`)!.pos = vec(centers[index]!.x, 60)
    })
    const selection: SelectionState = {
      hits: [
        wireHit(formals[2]!),
        nodeHit(nodes[0]!),
        wireHit(formals[0]!),
        nodeHit(nodes[1]!),
        nodeHit(nodes[2]!),
        wireHit(formals[1]!),
        nodeHit(nodes[3]!),
        wireHit(formals[3]!),
      ],
    }
    const gestures: ConnectionGesture[] = []
    const drag = controller(engine, selection, gestures)

    const founding = drag.claim(sample(centers[0]!, nodeHit(nodes[0]!)))!
    founding.move(sample(vec(-120, 80)))
    founding.release(sample(vec(-120, 80)), true)
    expect(selection.hits).toEqual([
      wireHit(formals[2]!),
      nodeHit(nodes[1]!),
      nodeHit(nodes[2]!),
      wireHit(formals[1]!),
      nodeHit(nodes[3]!),
      wireHit(formals[3]!),
    ])
    expect(drag.pendingState?.occurrences).toHaveLength(1)

    for (const index of [1, 2]) {
      const body = pendingBodyPoint(drag, drag.pendingState!)
      const branch = drag.claim(sample(body))!
      branch.move(sample(centers[index]!, nodeHit(nodes[index]!)))
      branch.release(sample(centers[index]!, nodeHit(nodes[index]!)), true)
    }
    expect(selection.hits).toEqual([
      nodeHit(nodes[3]!),
      wireHit(formals[3]!),
    ])

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
        occurrences: nodes.slice(0, 3).map((node, index) => ({
          sel: prepareSelectedOccurrences(diagram, [
            nodeHit(node),
            wireHit(formals[index]!),
          ])[0]!.occurrence.sel,
          args: [formals[index]!],
        })),
      },
    }])
    expect(drag.pendingState).toBeNull()
  })

  it('refuses a second contact on the same parsed occurrence', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const first = builder.ref(firstCut, 'Body', relSig([]))
    const second = builder.ref(secondCut, 'Body', relSig([]))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(first)!.pos = vec(-50, 0)
    engine.bodies.get(second)!.pos = vec(50, 0)
    const selection: SelectionState = {
      hits: [nodeHit(first), nodeHit(second)],
    }
    const refusals: string[] = []
    const drag = controller(engine, selection, [], refusals)

    const founding = drag.claim(sample(vec(-50, 0), nodeHit(first)))!
    founding.move(sample(vec(-50, 80)))
    founding.release(sample(vec(-50, 80)), true)
    const branch = drag.claim(sample(pendingBodyPoint(drag, drag.pendingState!)))!
    branch.move(sample(vec(-50, 0), nodeHit(first)))
    branch.release(sample(vec(-50, 0), nodeHit(first)), true)

    expect(refusals).toEqual(['that occurrence is already contacted by the pending relation wire'])
    expect(drag.pendingState?.occurrences).toHaveLength(1)
    expect(selection.hits).toEqual([nodeHit(second)])
  })

  it('lets the kernel refuse mismatched explicit occurrences and springs the loose end back', () => {
    const builder = new DiagramBuilder()
    const firstCut = builder.cut(builder.root)
    const secondCut = builder.cut(builder.root)
    const first = builder.ref(firstCut, 'FirstBody', UNARY)
    const second = builder.ref(secondCut, 'DifferentBody', UNARY)
    const firstFormal = builder.wire(firstCut, [{
      node: first,
      port: { kind: 'arg', index: 0 },
    }])
    const secondFormal = builder.wire(secondCut, [{
      node: second,
      port: { kind: 'arg', index: 0 },
    }])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.bodies.get(first)!.pos = vec(-50, 0)
    engine.bodies.get(second)!.pos = vec(50, 0)
    const selection: SelectionState = {
      hits: [
        nodeHit(first),
        wireHit(firstFormal),
        wireHit(secondFormal),
        nodeHit(second),
      ],
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

  it('derives contact geometry from the live contacted node owner', () => {
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
