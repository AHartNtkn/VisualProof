import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import type { Hit } from '../../src/app/hittest'
import {
  ProofMoveController,
  proofConnectionStep,
} from '../../src/app/interact/moves'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

function keySample(key: string) {
  return {
    key,
    shiftKey: false,
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

  it('constructs direct connection drags only as durable IOTA joins', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], IOTA)
    const right = builder.wire(negative, [], IOTA)
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
  })

  it('builds relation-wire merges through the same connection gesture', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], relSig([]))
    const right = builder.wire(negative, [], relSig([]))
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
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

  it('the i key is retired', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [])
    const right = builder.wire(negative, [])
    void left
    void right
    const diagram = builder.build()
    const { moves, applied } = harness(diagram)

    expect(moves.keyDown(keySample('i'))).toBe(false)
    expect(applied).toEqual([])
  })
})
