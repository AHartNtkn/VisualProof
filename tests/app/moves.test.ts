import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import type { Hit } from '../../src/app/hittest'
import { ProofMoveController } from '../../src/app/interact/moves'
import type { PointerSample } from '../../src/app/interact/viewport'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { relSig } from '../../src/kernel/diagram/sig'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { mkEngine } from '../../src/view/engine'
import { LIGHT } from '../../src/view/paint'
import { vec, type Vec2 } from '../../src/view/vec'
import { UNARY } from '../fixtures/zero-signature'

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

/** A minimal element double: enough DOM for the controller's prompts. */
function fakeElement(): {
  element: Record<string, unknown>
  listeners: Map<string, (event: unknown) => void>
} {
  const listeners = new Map<string, (event: unknown) => void>()
  const element: Record<string, unknown> = {
    style: {},
    append: () => undefined,
    remove: () => undefined,
    focus: () => undefined,
    setAttribute: () => undefined,
    addEventListener: (name: string, fn: (event: unknown) => void) => {
      listeners.set(name, fn)
    },
  }
  return { element, listeners }
}

function harness(diagram: Diagram, selection: readonly Hit[] = []) {
  const engine = mkEngine(diagram, [])
  const applied: ProofAction[] = []
  const refusals: string[] = []
  const inputs: ReturnType<typeof fakeElement>[] = []
  const host = {
    ownerDocument: {
      createElement: (tag: string) => {
        const made = fakeElement()
        if (tag === 'input') inputs.push(made)
        return made.element
      },
    },
    append: () => undefined,
  }
  const moves = new ProofMoveController({
    host: host as unknown as HTMLElement,
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
  return { moves, engine, applied, refusals, inputs }
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

  it('Delete on a lone wire deletes its ends; endpoint-free wires vacuous-eliminate', () => {
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
    const withEnds = harness(diagram, [{ kind: 'wire', id: shared }])

    expect(withEnds.moves.keyDown(keySample('Delete'))).toBe(true)
    expect(withEnds.refusals).toEqual([])
    expect(withEnds.applied).toHaveLength(1)
    expect(withEnds.applied[0]!.steps).toEqual([
      { rule: 'endsDelete', wire: shared },
    ])

    const bareBuilder = new DiagramBuilder()
    const bare = bareBuilder.wire(bareBuilder.root, [])
    const bareDiagram = bareBuilder.build()
    const bareCase = harness(bareDiagram, [{ kind: 'wire', id: bare }])

    expect(bareCase.moves.keyDown(keySample('Delete'))).toBe(true)
    expect(bareCase.applied).toHaveLength(1)
    expect(bareCase.applied[0]!.steps).toEqual([
      { rule: 'vacuousElim', wireId: bare },
    ])
  })

  it('Shift+W introduces a bare quantified wire through the arity prompt', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    builder.ref(cut, 'Marker', relSig([]))
    const diagram = builder.build()
    const { moves, engine, applied, inputs } = harness(diagram)
    engine.regions.set(cut, {
      center: vec(300, 200),
      radius: 120,
      support: [],
    })

    moves.passiveSample(pointerSample(vec(300, 200)))
    expect(moves.keyDown(keySample('W', true))).toBe(true)
    expect(applied).toEqual([])
    expect(inputs).toHaveLength(1)

    // Enter with a blank value picks an individual (ι) wire.
    inputs[0]!.element['value'] = ''
    inputs[0]!.listeners.get('keydown')!({ key: 'Enter' })

    expect(applied).toHaveLength(1)
    expect(applied[0]!.steps).toEqual([{
      rule: 'vacuousIntro',
      scope: cut,
      sig: { kind: 'iota' },
    }])
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
