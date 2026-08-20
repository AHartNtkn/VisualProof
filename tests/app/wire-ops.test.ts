import { describe, expect, it } from 'vitest'
import { WireOpsDragController } from '../../src/app/interact/wire-ops'
import { duplicateStep, fissionStep } from '../../src/app/interact/identity-ops'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig, type Sig } from '../../src/kernel/diagram/sig'
import { applyAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine, type Engine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import type { Vec2 } from '../../src/view/vec'
import {
  endpointPoint,
  farBlank,
  farStrandPoint,
  place,
  placeRegion,
  pointerSample,
} from './helpers/gesture'
import { segment, spread } from './helpers/build'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])

type Committed = { readonly label: string; readonly steps: readonly ProofStep[] }

function harness(diagram: Diagram, engine: Engine, promptedSig: Sig = IOTA) {
  const committed: Committed[] = []
  const refusals: string[] = []
  let current = diagram
  const controller = new WireOpsDragController({
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
    promptSig: (_client, apply) => { apply(promptedSig) },
    refuse: (text) => { refusals.push(text) },
  })
  return { controller, committed, refusals, diagram: () => current }
}

/** One left-drag: press at `from`, release at `to`. */
function drag(controller: WireOpsDragController, from: Vec2, to: Vec2): void {
  const claim = controller.claim(pointerSample(from))
  expect(claim).not.toBeNull()
  claim!.move(pointerSample(to))
  claim!.release(pointerSample(to), true)
}

function onlyStep(committed: readonly Committed[]): ProofStep {
  expect(committed).toHaveLength(1)
  expect(committed[0]!.steps).toHaveLength(1)
  return committed[0]!.steps[0]!
}

/**
 * A point radially between the apply-formal center zone (half the disc
 * radius) and the anchor's own halo, in the anchor's direction: lands in
 * the nearest-anchor band that reads as permute/duplicate.
 */
function bandPoint(engine: Engine, node: string, anchor: Vec2): Vec2 {
  const body = engine.bodies.get(node)!
  const disc = body.discR * engine.scale
  const dx = anchor.x - body.pos.x
  const dy = anchor.y - body.pos.y
  const anchorDistance = Math.hypot(dx, dy)
  const inner = disc / 2
  const outer = anchorDistance - 7
  expect(outer).toBeGreaterThan(inner)
  const d = (inner + outer) / 2
  return {
    x: body.pos.x + (dx / anchorDistance) * d,
    y: body.pos.y + (dy / anchorDistance) * d,
  }
}

/**
 * A binary relation wire applied at one atom, everything at the root:
 * the shared stage for the argument-plumbing rows. The atom is placed at
 * (300, 300) with its disc enlarged via the engine content scale so the
 * port/rim/center drop zones are geometrically distinct.
 */
function pluming() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, BINARY)
  const wire = builder.wire([
    { node: atom, port: { kind: 'head' } },
  ], BINARY)
  const wirePin = builder.pin(wire, builder.root)
  const first = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const firstPin = builder.pin(first, builder.root)
  const second = builder.wire([
    { node: atom, port: { kind: 'arg', index: 1 } },
  ])
  const secondPin = builder.pin(second, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, atom, { x: 300, y: 300 })
  place(engine, wirePin, { x: 300, y: 80 })
  place(engine, firstPin, { x: 100, y: 500 })
  place(engine, secondPin, { x: 500, y: 500 })
  const port = (index: number): Vec2 =>
    endpointPoint(
      engine,
      index === 0 ? first : second,
      { node: atom, port: { kind: 'arg', index } },
    )
  return { diagram, engine, atom, wire, first, second, port }
}

/**
 * `pluming()`'s shape, plus a second pin on the head wire ("the dot" the
 * atom's end is exposed onto) and a second pin on the first argument wire
 * ("the dot" that argument's end is exposed onto).
 */
function plumingWithDots() {
  const builder = new DiagramBuilder()
  const atom = builder.atom(builder.root, BINARY)
  const wire = builder.wire([
    { node: atom, port: { kind: 'head' } },
  ], BINARY)
  const wirePin = builder.pin(wire, builder.root)
  const headDot = builder.pin(wire, builder.root)
  const first = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const firstPin = builder.pin(first, builder.root)
  const argDot = builder.pin(first, builder.root)
  const second = builder.wire([
    { node: atom, port: { kind: 'arg', index: 1 } },
  ])
  const secondPin = builder.pin(second, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, atom, { x: 300, y: 300 })
  place(engine, wirePin, { x: 300, y: 80 })
  place(engine, headDot, { x: 700, y: 80 })
  place(engine, firstPin, { x: 100, y: 500 })
  place(engine, argDot, { x: 100, y: 750 })
  place(engine, secondPin, { x: 500, y: 500 })
  const port = (index: number): Vec2 =>
    endpointPoint(
      engine,
      index === 0 ? first : second,
      { node: atom, port: { kind: 'arg', index } },
    )
  return { diagram, engine, atom, wire, first, second, port, headDot, argDot, firstPin }
}

describe('expose: an atom/ref end or argument port dragged onto an identity dot on that wire', () => {
  it('an end dragged onto a dot on its own head wire commits identification-expose', () => {
    const { engine, diagram, atom } = plumingWithDots()
    const h = harness(diagram, engine)

    drag(h.controller, { x: 300, y: 300 }, { x: 700, y: 80 })

    expect(h.refusals).toEqual([])
    const step = onlyStep(h.committed)
    expect(step).toMatchObject({
      rule: 'identification',
      input: { kind: 'expose', transfer: [{ node: atom, port: { kind: 'head' } }] },
    })
  })

  it('an end dropped off-centre inside the dot\'s disc (clear of the strand halo) still commits expose, never parallelSplit', () => {
    const { engine, diagram, atom, headDot } = plumingWithDots()
    const h = harness(diagram, engine)
    const dotPos = engine.bodies.get(headDot)!.pos
    // 16 world units off the dot's own centre: inside its 54-unit disc,
    // well outside the 6-unit strand/endpoint hit halo, so no wire hit
    // exists at this exact point the way it does at the dot's own centre.
    const to = { x: dotPos.x, y: dotPos.y + 16 }

    drag(h.controller, { x: 300, y: 300 }, to)

    expect(h.refusals).toEqual([])
    const step = onlyStep(h.committed)
    expect(step).toMatchObject({
      rule: 'identification',
      input: { kind: 'expose', transfer: [{ node: atom, port: { kind: 'head' } }] },
    })
  })

  it('an argument port dragged onto a dot on its own argument wire commits identification-expose', () => {
    const { engine, diagram, atom, port } = plumingWithDots()
    const h = harness(diagram, engine)

    drag(h.controller, port(0), { x: 100, y: 750 })

    expect(h.refusals).toEqual([])
    const step = onlyStep(h.committed)
    expect(step).toMatchObject({
      rule: 'identification',
      input: { kind: 'expose', transfer: [{ node: atom, port: { kind: 'arg', index: 0 } }] },
    })
  })

  it('an end refuses on an identity dot that is not on this wire, with the reworded message', () => {
    const { engine, diagram } = plumingWithDots()
    const h = harness(diagram, engine)

    // firstPin is an identity dot, but it sits on the argument wire, not
    // on the atom's own head wire — the drop-target resolution fails.
    drag(h.controller, { x: 300, y: 300 }, { x: 100, y: 500 })

    expect(h.committed).toEqual([])
    expect(h.refusals).toEqual([
      'release on a parallel end, an own argument port, an identity dot on this wire, or open space',
    ])
  })
})

describe('object-typed drag dispatch', () => {
  it('strand onto another strand commits wireJoin', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = segment(builder, cut)
    const right = segment(builder, cut)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const from = spread(engine, left, { x: 100, y: 100 })
    const to = spread(engine, right, { x: 500, y: 100 })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'wireJoin',
      input: { a: left.wire, b: right.wire },
    })
  })

  it('joins relation wires through the same strand gesture', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const left = segment(builder, cut, relSig([]))
    const right = segment(builder, cut, relSig([]))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const from = spread(engine, left, { x: 100, y: 100 })
    const to = spread(engine, right, { x: 500, y: 100 })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'wireJoin',
      input: { a: left.wire, b: right.wire },
    })
  })

  it('strand onto an end of another wire commits a uniform argExtend', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const target = builder.wire([
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const grabbed = segment(builder, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    const from = spread(engine, grabbed, { x: 100, y: 500 })
    place(engine, atomB, { x: 700, y: 100 })
    const to = place(engine, atomA, { x: 300, y: 100 })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'argExtend',
      wire: target,
      position: 1,
      newArgSig: IOTA,
      attachments: { [atomA]: grabbed.wire, [atomB]: grabbed.wire },
    })
  })

  it('end onto a parallel end commits parallelFuse', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const headA = builder.wire([
      { node: atomA, port: { kind: 'head' } },
    ], UNARY)
    const headAPin = builder.pin(headA, builder.root)
    const headB = builder.wire([
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    const headBPin = builder.pin(headB, builder.root)
    const fusedArg = builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    // The fused atoms both die; the argument wire keeps its quantifier at
    // the sheet through pins, which is what lets the step through at all.
    builder.pin(fusedArg, builder.root)
    builder.pin(fusedArg, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    const from = place(engine, atomA, { x: 200, y: 100 })
    const to = place(engine, atomB, { x: 600, y: 100 })
    place(engine, headAPin, { x: 200, y: 400 })
    place(engine, headBPin, { x: 600, y: 400 })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'parallelFuse',
      a: headA,
      b: headB,
    })
  })

  it('end torn off into open space commits parallelSplit', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    const from = place(engine, atomA, { x: 200, y: 100 })
    place(engine, atomB, { x: 600, y: 100 })
    const h = harness(diagram, engine)

    drag(h.controller, from, farBlank())

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({ rule: 'parallelSplit', wire })
  })

  it('end onto one of its own argument ports commits identityLeaf', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const atom = builder.atom(scope, BINARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const wirePin = builder.pin(wire, scope)
    const first = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const firstPin = builder.pin(first, builder.root)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    const from = place(engine, atom, { x: 300, y: 300 })
    place(engine, wirePin, { x: 300, y: 80 })
    place(engine, firstPin, { x: 100, y: 500 })
    const to = endpointPoint(engine, first, {
      node: atom,
      port: { kind: 'arg', index: 0 },
    })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({ rule: 'identityLeaf', wire })
  })

  it('the rim (head terminal) pulled into open space commits arityShift via the prompt', () => {
    const { engine, diagram, wire, atom } = pluming()
    const from = endpointPoint(engine, wire, {
      node: atom,
      port: { kind: 'head' },
    })
    const h = harness(diagram, engine, IOTA)

    drag(h.controller, from, farBlank())

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'arityShift',
      wire,
      newArgSig: IOTA,
    })
  })

  it('refuses pulling the rim onto an identity dot\'s disc instead of committing the stub there', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, UNARY)
    const wire = builder.wire([{ node: atom, port: { kind: 'head' } }], UNARY)
    builder.pin(wire, builder.root)
    builder.wire([{ node: atom, port: { kind: 'arg', index: 0 } }])
    const dot = builder.identity(builder.root, IOTA, 1)
    const dotWire = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
    builder.pin(dotWire, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, atom, { x: 300, y: 300 })
    place(engine, dot, { x: 300, y: 700 })
    const from = endpointPoint(engine, wire, { node: atom, port: { kind: 'head' } })
    const h = harness(diagram, engine)
    const dotPos = engine.bodies.get(dot)!.pos
    const to = { x: dotPos.x, y: dotPos.y + 16 }

    drag(h.controller, from, to)

    expect(h.committed).toEqual([])
    expect(h.refusals).toEqual(['pull the new argument stub into open space'])
  })

  it('a port dragged off the node unshifts when its wire is a private stub', () => {
    const { engine, diagram, wire, port } = pluming()
    const h = harness(diagram, engine)

    // `first` has no other endpoint, so the unshift side condition holds.
    drag(h.controller, port(0), farBlank())

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'arityUnshift',
      wire,
      position: 0,
    })
  })

  it('a port dragged off the node drops when the unshift condition fails', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    const shared = builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    // Dropping the argument removes both incidences: the wire survives as
    // the bare segment its pins already hold at the sheet.
    builder.pin(shared, builder.root)
    builder.pin(shared, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, atomA, { x: 200, y: 100 })
    place(engine, atomB, { x: 600, y: 100 })
    const from = endpointPoint(engine, shared, {
      node: atomA,
      port: { kind: 'arg', index: 0 },
    })
    const h = harness(diagram, engine)

    drag(h.controller, from, farBlank())

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'argDrop',
      wire,
      position: 0,
    })
  })

  it('a port dropped onto its adjacent sibling with a shared wire commits argContract', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, BINARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const wirePin = builder.pin(wire, builder.root)
    const shared = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    // Contracting the two positions into one leaves a single incidence, so
    // the wire needs a pin to keep its quantifier at the sheet.
    builder.pin(shared, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, atom, { x: 300, y: 300 })
    place(engine, wirePin, { x: 300, y: 80 })
    const from = endpointPoint(engine, shared, {
      node: atom,
      port: { kind: 'arg', index: 0 },
    })
    const to = endpointPoint(engine, shared, {
      node: atom,
      port: { kind: 'arg', index: 1 },
    })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'argContract',
      wire,
      position: 0,
    })
  })

  it('a port dropped past its sibling, off the halo, commits the transposition', () => {
    const { engine, diagram, wire, atom, port } = pluming()
    // Land inside the disc, nearer position 1 than 0, but outside 1's halo.
    const toward = bandPoint(engine, atom, port(1))
    const h = harness(diagram, engine)

    drag(h.controller, port(0), toward)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'argPermute',
      wire,
      permutation: [1, 0],
    })
  })

  it('a port dropped beside itself commits argDuplicate', () => {
    const { engine, diagram, wire, atom, port } = pluming()
    // Inside the disc, still nearest its own anchor, beyond the halo.
    const beside = bandPoint(engine, atom, port(0))
    const h = harness(diagram, engine)

    drag(h.controller, port(0), beside)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'argDuplicate',
      wire,
      position: 0,
    })
  })

  it('a port dropped on its own end center commits applyFormal', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const higher = relSig([UNARY, IOTA])
    const atom = builder.atom(scope, higher)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], higher)
    const wirePin = builder.pin(wire, scope)
    const target = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    const targetPin = builder.pin(target, scope)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    const center = place(engine, atom, { x: 300, y: 300 })
    place(engine, wirePin, { x: 300, y: 80 })
    place(engine, targetPin, { x: 100, y: 500 })
    const from = endpointPoint(engine, target, {
      node: atom,
      port: { kind: 'arg', index: 0 },
    })
    const h = harness(diagram, engine)

    drag(h.controller, from, center)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'applyFormal',
      wire,
      position: 0,
    })
  })

  it('a cut ring dropped on the end it wraps commits cutAbsorb', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, UNARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const wirePin = builder.pin(wire, builder.root)
    const argWire = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(argWire, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    placeRegion(engine, cut, { x: 300, y: 300 }, 200)
    const to = place(engine, atom, { x: 300, y: 300 })
    place(engine, wirePin, { x: 300, y: 700 })
    const from = { x: 300, y: 100 }
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({ rule: 'cutAbsorb', wire })
  })

  it('springs back on a kernel refusal with the diagram unchanged', () => {
    // Joining at the root is gated off in the forward orientation.
    const builder = new DiagramBuilder()
    const left = segment(builder, builder.root)
    const right = segment(builder, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const from = spread(engine, left, { x: 100, y: 100 })
    const to = spread(engine, right, { x: 500, y: 100 })
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.committed).toEqual([])
    expect(h.refusals).toHaveLength(1)
    expect(h.diagram()).toBe(diagram)
  })
})

/** Three wires meeting at an arity-3 dot at the root, each held by a pin. */
function dotJoined3() {
  const builder = new DiagramBuilder()
  const dot = builder.identity(builder.root, IOTA, 3)
  const a = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
  const aPin = builder.pin(a, builder.root)
  const b = builder.wire([{ node: dot, port: { kind: 'identity', index: 1 } }])
  const bPin = builder.pin(b, builder.root)
  const c = builder.wire([{ node: dot, port: { kind: 'identity', index: 2 } }])
  const cPin = builder.pin(c, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot, { x: 300, y: 300 })
  place(engine, aPin, { x: 100, y: 300 })
  place(engine, bPin, { x: 500, y: 300 })
  place(engine, cPin, { x: 300, y: 540 })
  return { diagram, engine, dot, a, b, c }
}

/** Two wires `a` and `c` each threading through both `dot1` and `dot2` —
    their strands share two identity dots, not one. */
function ladderedDots() {
  const builder = new DiagramBuilder()
  const dot1 = builder.identity(builder.root, IOTA, 2)
  const dot2 = builder.identity(builder.root, IOTA, 2)
  const a = builder.wire([
    { node: dot1, port: { kind: 'identity', index: 0 } },
    { node: dot2, port: { kind: 'identity', index: 0 } },
  ])
  const aPin = builder.pin(a, builder.root)
  const c = builder.wire([
    { node: dot1, port: { kind: 'identity', index: 1 } },
    { node: dot2, port: { kind: 'identity', index: 1 } },
  ])
  const cPin = builder.pin(c, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot1, { x: 300, y: 300 })
  place(engine, dot2, { x: 300, y: 600 })
  place(engine, aPin, { x: 100, y: 450 })
  place(engine, cPin, { x: 500, y: 450 })
  return { diagram, engine, dot1, dot2, a, c }
}

/** A single-port dot on wire `a`. */
function singleDot() {
  const builder = new DiagramBuilder()
  const dot = builder.identity(builder.root, IOTA, 1)
  const a = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
  const aPin = builder.pin(a, builder.root)
  const diagram = builder.build()
  const engine = mkEngine(diagram, [])
  engine.scale = 12
  place(engine, dot, { x: 300, y: 300 })
  place(engine, aPin, { x: 100, y: 300 })
  return { diagram, engine, dot, a }
}

describe('fission: strand dragged onto another strand sharing a dot', () => {
  it('exactly one shared dot fissions it into two dots, the target wire becoming the bridge', () => {
    const { diagram, engine, dot, a, b, c } = dotJoined3()
    const from = farStrandPoint(engine, a)
    const to = farStrandPoint(engine, c)
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(h.committed).toHaveLength(1)
    expect(h.committed[0]!.steps).toEqual([fissionStep(diagram, dot, a, c)])
    const after = h.diagram()
    expect(Object.keys(after.wires).sort()).toEqual([a, b, c].sort())
    const identities = Object.entries(after.nodes).filter(([, n]) => n.kind === 'identity' && n.arity >= 2)
    expect(identities).toHaveLength(2)
    const portSets = identities.map(([id]) =>
      Object.entries(after.wires)
        .filter(([, w]) => w.endpoints.some((ep) => ep.node === id))
        .map(([wid]) => wid)
        .sort())
    expect(portSets.sort()).toEqual([[a, c].sort(), [b, c].sort()].sort())
  })

  it('refuses when the strands share several dots', () => {
    const { diagram, engine, a, c } = ladderedDots()
    const from = farStrandPoint(engine, a)
    const to = farStrandPoint(engine, c)
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.committed).toEqual([])
    expect(h.refusals).toEqual(['these lines meet at several dots'])
  })

  it('strands sharing no dot still commit wireJoin, unregressed', () => {
    // A cut, matching every other wireJoin test in this file: joining is
    // gated off at the root in the forward orientation (inner scope must
    // be negative).
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const dotA = builder.identity(cut, IOTA, 1)
    const left = builder.wire([{ node: dotA, port: { kind: 'identity', index: 0 } }])
    const leftPin = builder.pin(left, cut)
    const dotC = builder.identity(cut, IOTA, 1)
    const right = builder.wire([{ node: dotC, port: { kind: 'identity', index: 0 } }])
    const rightPin = builder.pin(right, cut)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, dotA, { x: 100, y: 100 })
    place(engine, leftPin, { x: 100, y: 400 })
    place(engine, dotC, { x: 500, y: 100 })
    place(engine, rightPin, { x: 500, y: 400 })
    const from = farStrandPoint(engine, left)
    const to = farStrandPoint(engine, right)
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(onlyStep(h.committed)).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
  })
})

describe('duplicate: strand dragged onto an identity dot it is attached to', () => {
  it('duplicates the wire onto the dot', () => {
    const { diagram, engine, dot, a } = singleDot()
    const from = farStrandPoint(engine, a)
    const to = engine.bodies.get(dot)!.pos
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.refusals).toEqual([])
    expect(h.committed[0]!.steps).toEqual([duplicateStep(diagram, dot, a)])
    const after = h.diagram()
    expect(after.nodes[dot]).toMatchObject({ kind: 'identity', arity: 2 })
    const onDot = after.wires[a]!.endpoints.filter((ep) => ep.node === dot)
    expect(onDot).toHaveLength(2)
  })

  it('refuses dropping on a dot the strand is not attached to', () => {
    const builder = new DiagramBuilder()
    const dot = builder.identity(builder.root, IOTA, 1)
    const a = builder.wire([{ node: dot, port: { kind: 'identity', index: 0 } }])
    const aPin = builder.pin(a, builder.root)
    const other = builder.identity(builder.root, IOTA, 1)
    const b = builder.wire([{ node: other, port: { kind: 'identity', index: 0 } }])
    const bPin = builder.pin(b, builder.root)
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    engine.scale = 12
    place(engine, dot, { x: 300, y: 300 })
    place(engine, aPin, { x: 100, y: 300 })
    place(engine, other, { x: 700, y: 300 })
    place(engine, bPin, { x: 900, y: 300 })
    const from = farStrandPoint(engine, a)
    const to = engine.bodies.get(other)!.pos
    const h = harness(diagram, engine)

    drag(h.controller, from, to)

    expect(h.committed).toEqual([])
    expect(h.refusals).toEqual(['this line is not attached to that dot'])
  })
})
