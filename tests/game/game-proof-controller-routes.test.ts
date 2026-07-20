import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection, type SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import { applyGameSteps, currentDiagram, startPuzzle } from '../../src/game/session'
import { puzzleId } from '../../src/game/types'
import {
  GameProofMoveController,
  vacuousEliminationChainSteps,
  type GameProofAction,
  type GameProofActionInput,
} from '../../src/game/interface/proof-moves'

const key = (value: Partial<{
  key: string; shiftKey: boolean; ctrlKey: boolean; altKey: boolean; metaKey: boolean; repeat: boolean
}> = {}) => ({ key: '', shiftKey: false, ctrlKey: false, altKey: false, metaKey: false, repeat: false, ...value })

const controllerFor = (
  diagram: ReturnType<DiagramBuilder['build']>,
  selection: { value: readonly { kind: 'node' | 'region' | 'wire'; id: string }[] },
  applied: ProofStep[],
  opened: string[],
  relations = new Map(),
) => new GameProofMoveController({
  host: { ownerDocument: {} } as HTMLElement,
  active: () => true,
  diagram: () => diagram,
  engine: () => mkEngine(diagram, []),
  selection: () => selection.value as never,
  setSelection: (next) => { selection.value = next as never },
  context: () => ({ theorems: new Map(), relations }),
  apply: (steps) => { applied.push(...steps) },
  refuse: (message) => { throw new Error(message) },
  theme: () => DARK,
  fuel: () => 256,
  openConstruction: (bubble) => { opened.push(bubble) },
})

describe('actual game proof controller routes', () => {
  it('recognizes only a gapless nested chain of selected vacuous bubble rims, deepest first', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const middle = builder.bubble(outer, 0)
    const inner = builder.bubble(middle, 0)
    const sibling = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const context = { theorems: new Map(), relations: new Map() }

    expect(vacuousEliminationChainSteps(diagram, [
      { kind: 'region', id: middle },
      { kind: 'region', id: inner },
      { kind: 'region', id: outer },
    ], context)).toEqual([
      { rule: 'vacuousElim', region: inner },
      { rule: 'vacuousElim', region: middle },
      { rule: 'vacuousElim', region: outer },
    ])
    expect(vacuousEliminationChainSteps(diagram, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
    ], context)).toBeNull()
    expect(vacuousEliminationChainSteps(diagram, [
      { kind: 'region', id: outer },
      { kind: 'region', id: sibling },
    ], context)).toBeNull()
  })

  it('commits selected nested vacuous bubbles as one prepared batch and clears selection once', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const middle = builder.bubble(outer, 0)
    const inner = builder.bubble(middle, 0)
    const diagram = builder.build()
    const batches: ProofStep[][] = []
    let cleared = 0
    const selection = { value: [outer, middle, inner].map((id) => ({ kind: 'region' as const, id })) }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => ({ theorems: new Map(), relations: new Map() }),
      apply: (steps) => { batches.push([...steps]) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(batches).toEqual([[
      { rule: 'vacuousElim', region: inner },
      { rule: 'vacuousElim', region: middle },
      { rule: 'vacuousElim', region: outer },
    ]])
    expect(cleared).toBe(1)
  })

  it('uses one proof-controller apply seam for one nested-rim gesture while appending every timeline step', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const middle = builder.bubble(outer, 0)
    const inner = builder.bubble(middle, 0)
    builder.termNode(inner, parseTerm('x'))
    const diagram = builder.build()
    const authority = { context: { theorems: new Map(), relations: new Map() } }
    let session = startPuzzle({ id: puzzleId('nested-vacuous-batch'), diagram })
    let applyCalls = 0
    const selection = { value: [outer, middle, inner].map((id) => ({ kind: 'region' as const, id })) }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => currentDiagram(session),
      engine: () => mkEngine(currentDiagram(session), []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => authority.context,
      apply: (steps) => {
        applyCalls++
        session = applyGameSteps(session, steps, authority).session
      },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(applyCalls).toBe(1)
    expect(session.timeline.steps).toEqual([
      { rule: 'vacuousElim', region: inner },
      { rule: 'vacuousElim', region: middle },
      { rule: 'vacuousElim', region: outer },
    ])
    expect(session.timeline.states).toHaveLength(4)
    expect(session.timeline.cursor).toBe(3)
  })

  it('preserves ordinary single-bubble keyboard elimination as a singleton batch', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const batches: ProofStep[][] = []
    const selection = { value: [{ kind: 'region' as const, id: bubble }] as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => ({ theorems: new Map(), relations: new Map() }),
      apply: (steps) => { batches.push([...steps]) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(batches).toEqual([[{ rule: 'vacuousElim', region: bubble }]])
  })

  it('does not recognize a nested selected chain when any bubble binds an atom', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const inner = builder.bubble(outer, 1)
    builder.atom(inner, inner)
    const diagram = builder.build()

    expect(vacuousEliminationChainSteps(diagram, [
      { kind: 'region', id: outer },
      { kind: 'region', id: inner },
    ], { theorems: new Map(), relations: new Map() })).toBeNull()
  })

  it('refuses atomically when a valid deepest elimination exposes a nonvacuous outer bubble', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 1)
    const inner = builder.bubble(outer, 0)
    builder.atom(inner, outer)
    const diagram = builder.build()
    const applied: ProofStep[][] = []
    const refusals: string[] = []
    let cleared = 0
    const original = [outer, inner].map((id) => ({ kind: 'region' as const, id }))
    const selection = { value: original as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => ({ theorems: new Map(), relations: new Map() }),
      apply: (steps) => { applied.push([...steps]) },
      refuse: (message) => { refusals.push(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Delete' }))).toBe(true)
    expect(applied).toEqual([])
    expect(selection.value).toBe(original)
    expect(cleared).toBe(0)
    expect(refusals).toEqual(['select one gapless chain of vacuous bubble rims'])
  })

  it('refuses an invalid multi-bubble batch without falling through or changing selection', () => {
    const builder = new DiagramBuilder()
    const first = builder.bubble(builder.root, 0)
    const second = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const applied: ProofStep[][] = []
    const refusals: string[] = []
    let cleared = 0
    const original = [first, second].map((id) => ({ kind: 'region' as const, id }))
    const selection = { value: original as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => ({ theorems: new Map(), relations: new Map() }),
      apply: (steps) => { applied.push([...steps]) },
      refuse: (message) => { refusals.push(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Delete' }))).toBe(true)
    expect(applied).toEqual([])
    expect(selection.value).toBe(original)
    expect(cleared).toBe(0)
    expect(refusals).toEqual(['select one gapless chain of vacuous bubble rims'])
  })

  it('refuses a mixed multi-bubble selection instead of deleting any generic sub-selection', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const inner = builder.bubble(outer, 0)
    const cut = builder.cut(inner)
    const diagram = builder.build()
    const applied: ProofStep[][] = []
    const refusals: string[] = []
    const original = [
      { kind: 'region' as const, id: outer },
      { kind: 'region' as const, id: inner },
      { kind: 'region' as const, id: cut },
    ]
    const selection = { value: original as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => ({ theorems: new Map(), relations: new Map() }),
      apply: (steps) => { applied.push([...steps]) },
      refuse: (message) => { refusals.push(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(applied).toEqual([])
    expect(selection.value).toBe(original)
    expect(refusals).toEqual(['select one gapless chain of vacuous bubble rims'])
  })

  it('claims iteration from a selected cut and commits that cut-rooted subtree', () => {
    const builder = new DiagramBuilder()
    const selectedCut = builder.cut(builder.root)
    const nestedCut = builder.cut(selectedCut)
    builder.termNode(nestedCut, parseTerm('x'))
    const diagram = builder.build()
    const applied: ProofStep[] = []
    const selected = { value: [{ kind: 'region' as const, id: selectedCut }] }
    const controller = controllerFor(diagram, selected, applied, [])
    const sample = {
      pointerId: 1,
      button: 0,
      client: { x: 10, y: 10 },
      screen: { x: 10, y: 10 },
      world: { x: 0, y: 0 },
      hit: { kind: 'region' as const, id: selectedCut },
      shiftKey: false,
      ctrlKey: false,
      altKey: false,
      metaKey: false,
    }

    const claim = controller.claim(sample)
    expect(claim).not.toBeNull()
    const release = {
      ...sample,
      client: { x: 100, y: 100 },
      screen: { x: 100, y: 100 },
      world: { x: 10_000, y: 10_000 },
      hit: null,
    }
    claim!.move(release)
    claim!.release(release, true)

    expect(applied).toEqual([{
      rule: 'iteration',
      sel: mkSelection(diagram, {
        region: builder.root,
        regions: [selectedCut],
        nodes: [],
        wires: [],
      }),
      target: builder.root,
    }])
  })

  it('commits every immediate GameProofAction through the shared controller dispatcher', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const inner = builder.cut(outer)
    const bubble = builder.bubble(builder.root, 0)
    const term = builder.termNode(builder.root, parseTerm('(\\x. x) y'))
    const ref = builder.ref(builder.root, 'R', 0)
    const diagram = builder.build()
    const wire = Object.keys(diagram.wires)[0]!
    const applied: ProofStep[] = []
    const opened: string[] = []
    const selected = { value: [] as { kind: 'node' | 'region' | 'wire'; id: string }[] }
    const relationBuilder = new DiagramBuilder()
    const relations = new Map([['R', mkDiagramWithBoundary(relationBuilder.build(), [])]])
    const controller = controllerFor(diagram, selected, applied, opened, relations)
    const selection = (region: string, regions: string[] = [], nodes: string[] = [], wires: string[] = []): SubgraphSelection =>
      mkSelection(diagram, { region, regions, nodes, wires })
    const invoke = (action: GameProofAction, sel: SubgraphSelection, input?: GameProofActionInput): void => {
      expect(controller.invokeAction(action, sel, input)).toBe(true)
    }

    invoke({ kind: 'erase', label: '' }, selection(builder.root, [outer]))
    invoke({ kind: 'insert', label: '' }, selection(builder.root), { kind: 'term', source: 'z' })
    invoke({ kind: 'doubleCutWrap', label: '' }, selection(builder.root, [], [term]))
    invoke({ kind: 'doubleCutElim', label: '' }, selection(builder.root, [outer]))
    invoke({ kind: 'vacuousWrap', label: '' }, selection(builder.root, [], [term]), { kind: 'arity', arity: 2 })
    invoke({ kind: 'vacuousElim', label: '' }, selection(builder.root, [bubble]))
    invoke({ kind: 'iterate', label: '' }, selection(builder.root, [], [term]), { kind: 'target', region: inner })
    invoke({ kind: 'deiterate', label: '' }, selection(builder.root, [], [term]))
    invoke({ kind: 'convert', label: '' }, selection(builder.root, [], [term]), { kind: 'conversion', source: 's0' })
    invoke({ kind: 'relUnfold', label: '' }, selection(builder.root, [], [ref]))
    expect(applied.map((step) => step.rule)).toEqual([
      'erasure', 'insertion', 'doubleCutIntro', 'doubleCutElim', 'vacuousIntro',
      'vacuousElim', 'iteration', 'deiteration', 'conversion', 'relUnfold',
    ])
    expect(wire).toBeTruthy()
  })

  it('routes named/construction instantiation and exact relation folding', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const ref = builder.ref(builder.root, 'R', 0)
    const diagram = builder.build()
    const bodyBuilder = new DiagramBuilder()
    bodyBuilder.ref(bodyBuilder.root, 'R', 0)
    const relations = new Map([['R', mkDiagramWithBoundary(bodyBuilder.build(), [])]])
    const applied: ProofStep[] = []
    const opened: string[] = []
    const selected = { value: [] as { kind: 'node' | 'region' | 'wire'; id: string }[] }
    const controller = controllerFor(diagram, selected, applied, opened, relations)
    const bubbleSelection = mkSelection(diagram, { region: builder.root, regions: [bubble], nodes: [], wires: [] })
    const refSelection = mkSelection(diagram, { region: builder.root, regions: [], nodes: [ref], wires: [] })

    expect(controller.invokeAction(
      { kind: 'instantiate', label: '' }, bubbleSelection, { kind: 'construction' },
    )).toBe(true)
    expect(controller.invokeAction(
      { kind: 'instantiate', label: '' }, bubbleSelection, { kind: 'relation', name: 'R' },
    )).toBe(true)
    expect(controller.invokeAction(
      { kind: 'relFold', label: '' }, refSelection, { kind: 'relation', name: 'R' },
    )).toBe(true)
    expect(opened).toEqual([bubble])
    expect(applied.map((step) => step.rule)).toEqual(['comprehensionInstantiate', 'relFold'])
  })

  it('routes actual F and double-click fusion once each', () => {
    const builder = new DiagramBuilder()
    const term = builder.termNode(builder.root, parseTerm('x'))
    const diagram = builder.build()
    const wire = Object.keys(diagram.wires)[0]!
    const applied: ProofStep[] = []
    const selected = { value: [{ kind: 'wire' as const, id: wire }] }
    const controller = controllerFor(diagram, selected, applied, [])
    expect(controller.keyDown(key({ key: 'F' }))).toBe(true)
    selected.value = [{ kind: 'wire', id: wire }]
    expect(controller.doubleClick({
      pointerId: 1, button: 0, client: { x: 1, y: 1 }, screen: { x: 1, y: 1 },
      world: { x: 1, y: 1 }, hit: { kind: 'wire', id: wire },
      shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    })).toBe(true)
    expect(applied).toEqual([{ rule: 'fusion', wire }, { rule: 'fusion', wire }])
    expect(term).toBeTruthy()
  })
})
