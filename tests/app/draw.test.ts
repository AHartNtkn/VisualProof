import { describe, expect, it } from 'vitest'
import { DrawGestureController } from '../../src/app/interact/draw'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Endpoint, Diagram, RegionId, WireId } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine, pkey, type Engine } from '../../src/view/engine'
import { computeLegs } from '../../src/view/wires'
import { LIGHT } from '../../src/view/paint'
import type { Vec2 } from '../../src/view/vec'

const UNARY = relSig([IOTA])

function sample(point: Vec2): PointerSample {
  return {
    pointerId: 1,
    button: 2,
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

type Committed = { readonly label: string; readonly steps: readonly ProofStep[] }

function harness(diagram: Diagram, engine: Engine) {
  const committed: Committed[] = []
  const refusals: string[] = []
  const spawns: RegionId[] = []
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
    refuse: (text) => { refusals.push(text) },
  })
  return {
    controller,
    committed,
    refusals,
    spawns,
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

/** World position of a wire's terminal at one endpoint. */
function endpointPoint(engine: Engine, wire: WireId, endpoint: Endpoint): Vec2 {
  const key = pkey(endpoint.port)
  for (const geometry of computeLegs(engine)) {
    if (geometry.leg.wid !== wire || geometry.pts.length === 0) continue
    if (geometry.leg.from.body === endpoint.node && geometry.leg.from.key === key) {
      return geometry.pts[0]!
    }
    if (geometry.leg.to.body === endpoint.node && geometry.leg.to.key === key) {
      return geometry.pts.at(-1)!
    }
  }
  throw new Error(`no leg terminal for ${wire} at ${endpoint.node}`)
}

function farBlank(): Vec2 {
  return { x: 4000, y: 4000 }
}

/**
 * The freshly built engine stacks every body near the origin; spread the
 * fixture out so each probe point touches exactly the intended object.
 */
function place(engine: Engine, bodyId: string, pos: Vec2): Vec2 {
  const body = engine.bodies.get(bodyId)
  if (body === undefined) throw new Error(`no body '${bodyId}'`)
  body.pos = pos
  return pos
}

function placeRegion(
  engine: Engine,
  region: RegionId,
  center: Vec2,
  radius: number,
): Vec2 {
  engine.regions.set(region, { center, radius, support: [] })
  return center
}

describe('drawing gesture dispatch', () => {
  it('spawn-ends: blank-site contacts commit vacuousIntro + endsSpawn', () => {
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
      rule: 'vacuousIntro',
      scope: diagram.root,
      sig: relSig([]),
    })
    expect(steps[1]).toMatchObject({
      rule: 'endsSpawn',
      sites: [{ region: cut, args: [] }],
    })
    const spawned = Object.keys(h.diagram().wires)
      .filter((id) => diagram.wires[id] === undefined)
    expect(spawned).toHaveLength(1)
    expect(h.diagram().wires[spawned[0]!]!.endpoints).toHaveLength(1)
  })

  it('sever: end contacts on one wire commit wireSever with the complement kept', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    builder.wire(builder.root, [{ node: atomA, port: { kind: 'head' } }], UNARY)
    builder.wire(builder.root, [{ node: atomB, port: { kind: 'head' } }], UNARY)
    const shared = builder.wire(builder.root, [
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
    const headA = builder.wire(builder.root, [{ node: atomA, port: { kind: 'head' } }], UNARY)
    const headB = builder.wire(builder.root, [{ node: atomB, port: { kind: 'head' } }], UNARY)
    builder.wire(builder.root, [
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
      builder.wire(builder.root, [{ node, port: { kind: 'identity', index: 0 } }])
      builder.wire(builder.root, [{ node, port: { kind: 'identity', index: 1 } }])
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
    const wireA = builder.wire(builder.root, [])
    const wireB = builder.wire(builder.root, [])
    const diagram = builder.build()
    const commitWith = (first: WireId, second: WireId) => {
      const engine = mkEngine(diagram, [])
      const dropAt = placeRegion(engine, cut, { x: 300, y: 200 }, 120)
      const pointFirst = place(engine, `j:${first}`, { x: 100, y: 500 })
      const pointSecond = place(engine, `j:${second}`, { x: 500, y: 500 })
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
      wires: [wireA, wireB].sort(),
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
    builder.wire(builder.root, [{ node, port: { kind: 'identity', index: 0 } }])
    builder.wire(builder.root, [{ node, port: { kind: 'identity', index: 1 } }])
    const other = builder.wire(builder.root, [])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const strandPoint = place(engine, `j:${other}`, { x: 500, y: 600 })
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
    builder.wire(cut, [{ node: atomA, port: { kind: 'head' } }], UNARY)
    builder.wire(cut, [{ node: atomB, port: { kind: 'head' } }], UNARY)
    const shared = builder.wire(cut, [
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

  it('a plain right-click with no drawing pending is not claimed as a gesture', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const h = harness(diagram, engine)

    const claim = h.controller.claim(sample({ x: 10, y: 10 }))!
    claim.release(sample({ x: 10, y: 10 }), false)

    expect(h.controller.hasPendingInteraction).toBe(false)
    // The palette must still open: nothing suppresses the context menu.
    expect(h.controller.consumeMenuSuppression()).toBe(false)
  })
})
