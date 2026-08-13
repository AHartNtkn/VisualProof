import { describe, expect, it } from 'vitest'
import { DrawGestureController } from '../../src/app/interact/draw'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Endpoint, Diagram, RegionId } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { bareWireAssembly } from '../../src/kernel/rules/identity-rules'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { Vec2 } from '../../src/view/vec'
import {
  endpointPoint,
  farBlank,
  place,
  placeRegion,
  pointerSample,
} from './helpers/gesture'
import { segment, spread, type Segment } from './helpers/build'

const UNARY = relSig([IOTA])

function sample(point: Vec2): PointerSample {
  return pointerSample(point, 2)
}

type Committed = { readonly label: string; readonly steps: readonly ProofStep[] }

function harness(diagram: Diagram, engine: Engine) {
  const committed: Committed[] = []
  const refusals: string[] = []
  const spawns: RegionId[] = []
  const stillMenus: PointerSample[] = []
  let current = diagram
  const controller = new DrawGestureController({
    active: () => true,
    engine: () => engine,
    diagram: () => current,
    viewScale: () => 1,
    theme: () => LIGHT,
    context: () => EMPTY_PROOF_CONTEXT,
    orientation: () => 'forward',
    commit: (label, steps) => {
      try {
        current = applyAction(
          current,
          { label, steps, placements: [] },
          EMPTY_PROOF_CONTEXT,
          'forward',
        )
      } catch (error) {
        refusals.push(error instanceof Error ? error.message : String(error))
        return false
      }
      committed.push({ label, steps })
      return true
    },
    openSpawn: (_sample, region) => { spawns.push(region) },
    stillMenu: (sample) => { stillMenus.push(sample) },
    refuse: (text) => { refusals.push(text) },
  })
  return {
    controller,
    committed,
    refusals,
    spawns,
    stillMenus,
    diagram: () => current,
  }
}

/** Drive one founding stroke: press at `from`, release at `to`. */
function stroke(
  controller: DrawGestureController,
  from: Vec2,
  to: Vec2,
): void {
  const claim = controller.claim(sample(from))
  expect(claim).not.toBeNull()
  claim!.move(sample(to))
  claim!.release(sample(to), true)
}

/** A still right-click while a drawing is pending adds a contact. */
function clickContact(controller: DrawGestureController, at: Vec2): void {
  const claim = controller.claim(sample(at))
  expect(claim).not.toBeNull()
  claim!.release(sample(at), false)
}

/** Grab the pending loose end at `loose` and drop it at `to` (commit). */
function drop(controller: DrawGestureController, loose: Vec2, to: Vec2): void {
  const claim = controller.claim(sample(loose))
  expect(claim).not.toBeNull()
  claim!.move(sample(to))
  claim!.release(sample(to), true)
}


describe('drawing gesture dispatch', () => {
  it('spawn-ends: blank-site contacts commit vacuity insertion + endsSpawn', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const inCut = placeRegion(engine, cut, { x: 300, y: 200 }, 120)
    const h = harness(diagram, engine)

    // Founding stroke lands on nothing: the loose end parks at the release.
    stroke(h.controller, { x: 3900, y: 3900 }, farBlank())
    // One blank site inside the cut, then drop the loose end at the root.
    clickContact(h.controller, inCut)
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    const steps = h.committed[0]!.steps
    expect(steps).toHaveLength(2)
    expect(steps[0]).toEqual({
      rule: 'vacuity',
      direction: 'insert',
      assembly: bareWireAssembly('w', diagram.root, relSig([]), ['pin0', 'pin1']),
    })
    expect(steps[1]).toMatchObject({
      rule: 'endsSpawn',
      sites: [{ region: cut, args: [] }],
    })
    const spawned = Object.keys(h.diagram().wires)
      .filter((id) => diagram.wires[id] === undefined)
    expect(spawned).toHaveLength(1)
    // The stroke's own two pins at the sheet, plus the end spawned in the cut.
    expect(h.diagram().wires[spawned[0]!]!.endpoints).toHaveLength(3)
  })

  it('sever: end contacts on one wire commit wireSever with the complement kept', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    builder.wire([{ node: atomA, port: { kind: 'head' } }], UNARY)
    builder.wire([{ node: atomB, port: { kind: 'head' } }], UNARY)
    const shared = builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    place(engine, atomA, { x: 100, y: 100 })
    place(engine, atomB, { x: 500, y: 100 })
    const contactA: Endpoint = { node: atomA, port: { kind: 'arg', index: 0 } }
    const h = harness(diagram, engine)

    stroke(h.controller, farBlank(), endpointPoint(engine, shared, contactA))
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    expect(h.committed[0]!.steps).toEqual([{
      rule: 'wireSever',
      input: {
        wire: shared,
        keep: [{ node: atomB, port: { kind: 'arg', index: 0 } }],
        scope: diagram.root,
      },
    }])
  })

  it('abstract-formal: applied ends of different wires commit abstractFormal', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const headA = builder.wire([{ node: atomA, port: { kind: 'head' } }], UNARY)
    const headB = builder.wire([{ node: atomB, port: { kind: 'head' } }], UNARY)
    builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    place(engine, atomA, { x: 200, y: 260 })
    place(engine, atomB, { x: 400, y: 260 })
    const pointA = endpointPoint(engine, headA, { node: atomA, port: { kind: 'head' } })
    const pointB = endpointPoint(engine, headB, { node: atomB, port: { kind: 'head' } })
    const h = harness(diagram, engine)

    stroke(h.controller, farBlank(), pointA)
    clickContact(h.controller, pointB)
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    const step = h.committed[0]!.steps[0]!
    expect(step.rule).toBe('abstractFormal')
    if (step.rule !== 'abstractFormal') throw new Error('unreachable')
    expect([...step.ends].sort()).toEqual([atomA, atomB].sort())
    expect(step.scope).toBe(diagram.root)
  })

  it('identity abstract: identity-node contacts commit identityAbstract', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const nodeA = builder.identity(cut, IOTA, 2)
    const nodeB = builder.identity(cut, IOTA, 2)
    for (const node of [nodeA, nodeB]) {
      builder.wire([{ node, port: { kind: 'identity', index: 0 } }])
      builder.wire([{ node, port: { kind: 'identity', index: 1 } }])
    }
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const pointA = place(engine, nodeA, { x: 100, y: 300 })
    const pointB = place(engine, nodeB, { x: 500, y: 300 })
    const h = harness(diagram, engine)

    stroke(h.controller, farBlank(), pointA)
    clickContact(h.controller, pointB)
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    const step = h.committed[0]!.steps[0]!
    expect(step.rule).toBe('identityAbstract')
    if (step.rule !== 'identityAbstract') throw new Error('unreachable')
    expect([...step.nodes].sort()).toEqual([nodeA, nodeB].sort())
    expect(step.scope).toBe(diagram.root)
  })

  it('identity insertion: strand contacts commit identityInsert in canonical order', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const wireA = segment(builder, builder.root)
    const wireB = segment(builder, builder.root)
    const diagram = builder.build()
    const commitWith = (first: Segment, second: Segment) => {
      const engine = mkEngine(diagram, [])
      const dropAt = placeRegion(engine, cut, { x: 300, y: 200 }, 120)
      const pointFirst = spread(engine, first, { x: 100, y: 500 })
      const pointSecond = spread(engine, second, { x: 500, y: 500 })
      const h = harness(diagram, engine)
      stroke(h.controller, farBlank(), pointFirst)
      clickContact(h.controller, pointSecond)
      drop(h.controller, farBlank(), dropAt)
      expect(h.refusals).toEqual([])
      expect(h.committed).toHaveLength(1)
      return h.committed[0]!.steps[0]!
    }

    // The committed step never depends on contact order (canonical-order pin).
    const forward = commitWith(wireA, wireB)
    const reversed = commitWith(wireB, wireA)

    expect(forward).toEqual(reversed)
    expect(forward).toEqual({
      rule: 'identityInsert',
      region: cut,
      wires: [wireA.wire, wireB.wire].sort(),
    })
  })

  it('nothing: a contactless drop opens the spawn prompt at the drop region', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const h = harness(diagram, engine)

    stroke(h.controller, { x: 3900, y: 3900 }, farBlank())
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.committed).toEqual([])
    expect(h.spawns).toEqual([diagram.root])
    expect(h.controller.hasPendingInteraction).toBe(false)
  })

  it('refuses a mixed contact set by type, keeping the drawing pending', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const node = builder.identity(cut, IOTA, 2)
    builder.wire([{ node, port: { kind: 'identity', index: 0 } }])
    builder.wire([{ node, port: { kind: 'identity', index: 1 } }])
    const other = segment(builder, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const strandPoint = spread(engine, other, { x: 500, y: 600 })
    const nodePoint = place(engine, node, { x: 100, y: 600 })
    const h = harness(diagram, engine)

    stroke(h.controller, farBlank(), strandPoint)
    clickContact(h.controller, nodePoint)
    drop(h.controller, farBlank(), { x: 4100, y: 4100 })

    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.refusals[0]).toMatch(/cannot mix/)
    expect(h.controller.hasPendingInteraction).toBe(true)
  })

  it('springs back on a kernel refusal, keeping the drawing pending', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atomA = builder.atom(cut, UNARY)
    const atomB = builder.atom(cut, UNARY)
    builder.wire([{ node: atomA, port: { kind: 'head' } }], UNARY)
    builder.wire([{ node: atomB, port: { kind: 'head' } }], UNARY)
    const shared = builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const dropAt = placeRegion(engine, cut, { x: 300, y: 200 }, 150)
    place(engine, atomA, { x: 200, y: 260 })
    place(engine, atomB, { x: 400, y: 260 })
    const contact: Endpoint = { node: atomA, port: { kind: 'arg', index: 0 } }
    const h = harness(diagram, engine)

    // Severing at a negative scope is gated off in the forward orientation.
    stroke(h.controller, farBlank(), endpointPoint(engine, shared, contact))
    drop(h.controller, farBlank(), dropAt)

    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.controller.hasPendingInteraction).toBe(true)
  })

  it('a closed founding stroke around one end commits cutWrap', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const wirePin = builder.pin(wire, builder.root)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    place(engine, atom, { x: 300, y: 300 })
    place(engine, wirePin, { x: 300, y: 80 })
    const h = harness(diagram, engine)

    const claim = h.controller.claim(sample({ x: 200, y: 200 }))!
    for (const point of [
      { x: 400, y: 200 },
      { x: 400, y: 400 },
      { x: 200, y: 400 },
      { x: 202, y: 203 },
    ]) claim.move(sample(point))
    claim.release(sample({ x: 202, y: 203 }), true)

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    expect(h.committed[0]!.steps).toEqual([{ rule: 'cutWrap', wire }])
    expect(h.controller.hasPendingInteraction).toBe(false)
  })

  it('a closed stroke around ends of different wires refuses', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    builder.wire([{ node: atomA, port: { kind: 'head' } }], UNARY)
    builder.wire([{ node: atomB, port: { kind: 'head' } }], UNARY)
    builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    place(engine, atomA, { x: 280, y: 300 })
    place(engine, atomB, { x: 320, y: 300 })
    const h = harness(diagram, engine)

    const claim = h.controller.claim(sample({ x: 200, y: 200 }))!
    for (const point of [
      { x: 400, y: 200 },
      { x: 400, y: 400 },
      { x: 200, y: 400 },
      { x: 202, y: 203 },
    ]) claim.move(sample(point))
    claim.release(sample({ x: 202, y: 203 }), true)

    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.refusals[0]).toMatch(/one wire/)
    expect(h.controller.hasPendingInteraction).toBe(false)
  })

  it('a plain right-click suppresses the raw event and reopens the palette', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const h = harness(diagram, engine)

    const claim = h.controller.claim(sample({ x: 10, y: 10 }))!
    // The browser contextmenu event (possibly fired at press time) is
    // consumed by the claim; the still release reopens through stillMenu.
    expect(h.controller.consumeMenuSuppression()).toBe(true)
    claim.release(sample({ x: 10, y: 10 }), false)

    expect(h.controller.hasPendingInteraction).toBe(false)
    expect(h.stillMenus).toHaveLength(1)
  })
})
