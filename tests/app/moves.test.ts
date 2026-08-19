import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import type { Hit } from '../../src/app/hittest'
import { ProofMoveController } from '../../src/app/interact/moves'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { bareWireDeletionSteps, bareWireInsertSteps } from '../../src/kernel/proof/bare-wire'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofStep } from '../../src/kernel/proof/step'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'
import { segment } from './helpers/build'
import { place } from './helpers/gesture'

function keySample(key: string, shiftKey = false) {
  return {
    key,
    shiftKey,
    ctrlKey: false,
    altKey: false,
    metaKey: false,
    repeat: false,
  }
}

function pointerSample(point: Vec2, hit: Hit | null = null): PointerSample {
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

function harness(diagram: Diagram, selection: readonly Hit[] = []) {
  const engine = mkEngine(diagram, [])
  const applied: ProofAction[] = []
  const refusals: string[] = []
  const moves = new ProofMoveController({
    host: { ownerDocument: {} } as unknown as HTMLElement,
    active: () => true,
    diagram: () => diagram,
    engine: () => engine,
    viewScale: () => 1,
    selection: () => selection,
    setSelection: () => undefined,
    context: () => EMPTY_PROOF_CONTEXT,
    orientation: () => 'forward',
    apply: (action) => { applied.push(action) },
    refuse: (text) => { refusals.push(text) },
    theme: () => LIGHT,
    fuel: () => 0,
    openSpawn: () => undefined,
  })
  return { moves, engine, applied, refusals }
}

describe('proof move vocabulary', () => {
  it('discovers only structural descriptors', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'Unknown', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const kinds = applicableActions(diagram, selection, EMPTY_PROOF_CONTEXT)
      .map((action) => action.kind)
    expect(kinds).toContain('erase')
    expect(kinds).toContain('iterate')
    expect(kinds).not.toContain('convert')
    expect(kinds).not.toContain('instantiate')
    expect(kinds).not.toContain('abstract')
    expect(kinds).not.toContain('relationJoin')
    expect(kinds).not.toContain('relationSever')
  })

  it('W with an empty selection spawns a double cut at the hovered region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    builder.ref(cut, 'Marker', relSig([]))
    const diagram = builder.build()
    const { moves, engine, applied } = harness(diagram)
    engine.regions.set(cut, {
      center: vec(300, 200),
      radius: 120,
      support: [],
    })

    moves.passiveSample(pointerSample(vec(300, 200)))
    expect(moves.keyDown(keySample('w'))).toBe(true)

    expect(applied).toHaveLength(1)
    expect(applied[0]!.steps).toEqual([{
      rule: 'doubleCutIntro',
      sel: { region: cut, regions: [], nodes: [], wires: [] },
    }])
  })

  it('W with a selection still wraps the selection', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'Marker', relSig([]))
    const diagram = builder.build()
    const { moves, applied } = harness(diagram, [{ kind: 'node', id: node }])

    expect(moves.keyDown(keySample('w'))).toBe(true)

    expect(applied).toHaveLength(1)
    expect(applied[0]!.steps[0]).toMatchObject({ rule: 'doubleCutIntro' })
  })

  it('Delete on a lone wire deletes its ends; bare segments vacuity-delete', () => {
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
    const withEnds = harness(diagram, [{ kind: 'wire', id: shared }])

    expect(withEnds.moves.keyDown(keySample('Delete'))).toBe(true)
    expect(withEnds.refusals).toEqual([])
    expect(withEnds.applied).toHaveLength(1)
    expect(withEnds.applied[0]!.steps).toEqual([
      { rule: 'endsDelete', wire: shared },
    ])

    // A bare segment's pins are its drawn ends, so they come into the
    // selection with it — and that is the shape vacuity deletes.
    const bareBuilder = new DiagramBuilder()
    const bare = segment(bareBuilder, bareBuilder.root)
    const bareDiagram = bareBuilder.build()
    const bareCase = harness(bareDiagram, [
      { kind: 'wire', id: bare.wire },
      { kind: 'node', id: bare.ends[0] },
      { kind: 'node', id: bare.ends[1] },
    ])

    expect(bareCase.moves.keyDown(keySample('Delete'))).toBe(true)
    expect(bareCase.refusals).toEqual([])
    expect(bareCase.applied).toHaveLength(1)
    expect(bareCase.applied[0]!.steps)
      .toEqual(bareWireDeletionSteps(bareDiagram, bare.wire))
  })

  it('Q spawns a bare quantifier wire at the hovered region', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    builder.ref(cut, 'Marker', relSig([]))
    const diagram = builder.build()
    const { moves, engine, applied } = harness(diagram)
    engine.regions.set(cut, {
      center: vec(300, 200),
      radius: 120,
      support: [],
    })

    moves.passiveSample(pointerSample(vec(300, 200)))
    expect(moves.keyDown(keySample('q'))).toBe(true)

    expect(applied).toHaveLength(1)
    expect(applied[0]!.steps).toEqual(
      [...bareWireInsertSteps(diagram, cut, IOTA, 'w', ['pin0', 'pin1']).steps],
    )
  })

  it('Shift+Q spawns a floating proposition quantifier there', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    builder.ref(cut, 'Marker', relSig([]))
    const diagram = builder.build()
    const { moves, engine, applied } = harness(diagram)
    engine.regions.set(cut, {
      center: vec(300, 200),
      radius: 120,
      support: [],
    })

    moves.passiveSample(pointerSample(vec(300, 200)))
    expect(moves.keyDown(keySample('Q', true))).toBe(true)

    expect(applied).toHaveLength(1)
    expect(applied[0]!.steps).toEqual(
      [...bareWireInsertSteps(diagram, cut, relSig([]), 'w', ['pin0', 'pin1']).steps],
    )
  })

  it('a right-drag slash across a leg commits wireSever', () => {
    const builder = new DiagramBuilder()
    const seg = segment(builder, builder.root)
    const diagram = builder.build()
    const { moves, engine, applied } = harness(diagram)
    place(engine, seg.ends[0], { x: 100, y: 300 })
    place(engine, seg.ends[1], { x: 500, y: 300 })
    const at = (p: Vec2) => ({ ...pointerSample(p), button: 2 })
    const claim = moves.claim(at({ x: 150, y: 100 }))
    expect(claim).not.toBeNull()
    claim!.move(at({ x: 150, y: 500 }))
    claim!.release(at({ x: 150, y: 500 }), true)
    expect(applied).toHaveLength(1)
    const steps = applied[0]!.steps
    expect(steps.length).toBeGreaterThan(0)
    expect(steps.every((step) => step.rule === 'wireSever')).toBe(true)
    const input = (steps[0] as Extract<ProofStep, { rule: 'wireSever' }>).input
    expect(input.wire).toBe(seg.wire)
    expect(input.keep).toHaveLength(1)   // one end severed, one kept
    expect(input.scope).toBeUndefined()  // derived-scope default
  })

  it('the i key is retired', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = segment(builder, negative)
    const right = segment(builder, negative)
    void left
    void right
    const diagram = builder.build()
    const { moves, applied } = harness(diagram)

    expect(moves.keyDown(keySample('i'))).toBe(false)
    expect(applied).toEqual([])
  })
})
