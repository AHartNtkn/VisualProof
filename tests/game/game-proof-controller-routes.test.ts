import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { portKey } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection, type SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT, extendRelations } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import { applyGameAction, currentDiagram, startPuzzle } from '../../src/game/session'
import { puzzleId } from '../../src/game/types'
import type { ActionDescriptor } from '../../src/interaction/actions'
import { FakeDocument, FakeElement } from './interface-fake-dom'
import {
  GameProofMoveController,
  vacuousEliminationChainSteps,
  type GameProofActionInput,
} from '../../src/game/interface/proof-moves'

const key = (value: Partial<{
  key: string; shiftKey: boolean; ctrlKey: boolean; altKey: boolean; metaKey: boolean; repeat: boolean
}> = {}) => ({ key: '', shiftKey: false, ctrlKey: false, altKey: false, metaKey: false, repeat: false, ...value })

const controllerFor = (
  diagram: ReturnType<DiagramBuilder['build']>,
  selection: { value: readonly { kind: 'node' | 'region' | 'wire'; id: string }[] },
  applied: ProofAction[],
  opened: string[],
  relations = new Map(),
) => new GameProofMoveController({
  host: { ownerDocument: {} } as HTMLElement,
  active: () => true,
  diagram: () => diagram,
  engine: () => mkEngine(diagram, []),
  viewScale: () => 1,
  selection: () => selection.value as never,
  setSelection: (next) => { selection.value = next as never },
  context: () => extendRelations(EMPTY_PROOF_CONTEXT, relations),
  apply: (action) => { applied.push(action) },
  refuse: (message) => { throw new Error(message) },
  theme: () => DARK,
  fuel: () => 256,
  openConstruction: (bubble) => { opened.push(bubble) },
})

const stepsFrom = (actions: readonly ProofAction[]) => actions.flatMap(({ steps }) => steps)

class MenuElement extends FakeElement {
  value = ''
  get childElementCount(): number { return this.children.length }
  focus(): void {}
}

class MenuDocument extends FakeDocument {
  override createElement(tagName: string): MenuElement {
    return new MenuElement(this, tagName.toUpperCase())
  }
}

const pointerSample = (
  hit: { readonly kind: 'node' | 'region' | 'wire'; readonly id: string } | null,
  world = { x: 0, y: 0 },
) => ({
  pointerId: 1,
  button: 2,
  client: { x: 10, y: 10 },
  screen: { x: 10, y: 10 },
  world,
  hit,
  shiftKey: false,
  ctrlKey: false,
  altKey: false,
  metaKey: false,
})

const clickMenuAction = (host: MenuElement, label: string): void => {
  const buttons = host.querySelectorAll<MenuElement>('.curse-proof-menu__action')
  const button = buttons.find((candidate) => candidate.textContent === label)
  if (button === undefined) {
    const descendants = host.querySelectorAll<MenuElement>('button')
    throw new Error(
      `missing context-menu action '${label}'; actions: ${buttons.map(({ textContent }) => textContent).join(', ')}; buttons: ${descendants.map(({ textContent }) => textContent).join(', ')}; host children: ${host.children.map(({ className }) => className).join(', ')}`,
    )
  }
  button.dispatchEvent(new Event('click'))
}

describe('actual game proof controller routes', () => {
  it('recognizes only a gapless nested chain of selected vacuous bubble rims, deepest first', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const middle = builder.bubble(outer, 0)
    const inner = builder.bubble(middle, 0)
    const sibling = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const context = EMPTY_PROOF_CONTEXT

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
    const batches: ProofAction[] = []
    let cleared = 0
    const selection = { value: [outer, middle, inner].map((id) => ({ kind: 'region' as const, id })) }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { batches.push(action) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(batches).toEqual([{
      label: 'vacuousElim + vacuousElim + vacuousElim',
      steps: [
        { rule: 'vacuousElim', region: inner },
        { rule: 'vacuousElim', region: middle },
        { rule: 'vacuousElim', region: outer },
      ],
      placements: [],
    }])
    expect(cleared).toBe(1)
  })

  it('uses one proof-controller apply seam and records one compound timeline action for one nested-rim gesture', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 0)
    const middle = builder.bubble(outer, 0)
    const inner = builder.bubble(middle, 0)
    builder.termNode(inner, parseTerm('x'))
    const diagram = builder.build()
    const authority = { context: EMPTY_PROOF_CONTEXT }
    let session = startPuzzle({ id: puzzleId('nested-vacuous-batch'), diagram })
    let applyCalls = 0
    const selection = { value: [outer, middle, inner].map((id) => ({ kind: 'region' as const, id })) }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => currentDiagram(session),
      engine: () => mkEngine(currentDiagram(session), []),
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => authority.context,
      apply: (action) => {
        applyCalls++
        session = applyGameAction(session, action, authority).session
      },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(applyCalls).toBe(1)
    expect(session.timeline.actions).toEqual([{
      label: 'vacuousElim + vacuousElim + vacuousElim',
      steps: [
        { rule: 'vacuousElim', region: inner },
        { rule: 'vacuousElim', region: middle },
        { rule: 'vacuousElim', region: outer },
      ],
      placements: [],
    }])
    expect(session.timeline.states).toHaveLength(2)
    expect(session.timeline.cursor).toBe(1)
  })

  it('preserves ordinary single-bubble keyboard elimination as a singleton batch', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const batches: ProofAction[] = []
    const selection = { value: [{ kind: 'region' as const, id: bubble }] as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { batches.push(action) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })

    expect(controller.keyDown(key({ key: 'Backspace' }))).toBe(true)
    expect(batches).toEqual([{
      label: 'vacuousElim',
      steps: [{ rule: 'vacuousElim', region: bubble }],
      placements: [],
    }])
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
    ], EMPTY_PROOF_CONTEXT)).toBeNull()
  })

  it('refuses atomically when a valid deepest elimination exposes a nonvacuous outer bubble', () => {
    const builder = new DiagramBuilder()
    const outer = builder.bubble(builder.root, 1)
    const inner = builder.bubble(outer, 0)
    builder.atom(inner, outer)
    const diagram = builder.build()
    const applied: ProofAction[] = []
    const refusals: string[] = []
    let cleared = 0
    const original = [outer, inner].map((id) => ({ kind: 'region' as const, id }))
    const selection = { value: original as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { applied.push(action) },
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
    const applied: ProofAction[] = []
    const refusals: string[] = []
    let cleared = 0
    const original = [first, second].map((id) => ({ kind: 'region' as const, id }))
    const selection = { value: original as readonly { kind: 'region'; id: string }[] }
    const controller = new GameProofMoveController({
      host: { ownerDocument: {} } as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never; cleared++ },
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { applied.push(action) },
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
    const applied: ProofAction[] = []
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
      viewScale: () => 1,
      selection: () => selection.value,
      setSelection: (next) => { selection.value = next as never },
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { applied.push(action) },
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
    const applied: ProofAction[] = []
    const selected = { value: [{ kind: 'region' as const, id: selectedCut }] }
    const controller = controllerFor(diagram, selected, applied, [])
    const sample = {
      pointerId: 1,
      button: 0,
      client: { x: 10, y: 10 },
      screen: { x: 10, y: 10 },
      world: { x: 10_000, y: 10_000 },
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
      label: 'iteration',
      steps: [{
        rule: 'iteration',
        sel: mkSelection(diagram, {
          region: builder.root,
          regions: [selectedCut],
          nodes: [],
          wires: [],
        }),
        target: builder.root,
      }],
      placements: [],
    }])
  })

  it('commits every immediate action descriptor through the shared controller dispatcher', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const inner = builder.cut(outer)
    const bubble = builder.bubble(builder.root, 0)
    const term = builder.termNode(builder.root, parseTerm('(\\x. x) y'))
    const deiterateRegion = builder.cut(builder.root)
    builder.cut(deiterateRegion)
    const justifierRegion = builder.cut(builder.root)
    builder.cut(justifierRegion)
    const ref = builder.ref(builder.root, 'R', 0)
    const diagram = builder.build()
    const wire = Object.keys(diagram.wires)[0]!
    const applied: ProofAction[] = []
    const opened: string[] = []
    const selected = { value: [] as { kind: 'node' | 'region' | 'wire'; id: string }[] }
    const relationBuilder = new DiagramBuilder()
    const relations = new Map([['R', mkDiagramWithBoundary(relationBuilder.build(), [])]])
    const controller = controllerFor(diagram, selected, applied, opened, relations)
    const selection = (region: string, regions: string[] = [], nodes: string[] = [], wires: string[] = []): SubgraphSelection =>
      mkSelection(diagram, { region, regions, nodes, wires })
    const invoke = (action: ActionDescriptor, sel: SubgraphSelection, input?: GameProofActionInput): void => {
      expect(controller.invokeAction(action, sel, input)).toBe(true)
    }

    invoke({ kind: 'erase', label: '' }, selection(builder.root, [outer]))
    invoke({ kind: 'doubleCutWrap', label: '' }, selection(builder.root, [], [term]))
    invoke({ kind: 'doubleCutElim', label: '' }, selection(builder.root, [outer]))
    invoke({ kind: 'vacuousElim', label: '' }, selection(builder.root, [bubble]))
    invoke({ kind: 'iterate', label: '', needsTarget: true }, selection(builder.root, [], [term]), { kind: 'target', region: inner })
    invoke({ kind: 'deiterate', label: '' }, selection(builder.root, [deiterateRegion]))
    invoke({ kind: 'convert', label: '', needsInput: 'term' }, selection(builder.root, [], [term]), { kind: 'conversion', source: 's0' })
    invoke({ kind: 'relUnfold', label: '' }, selection(builder.root, [], [ref]))
    expect(stepsFrom(applied).map((step) => step.rule)).toEqual([
      'erasure', 'doubleCutIntro', 'doubleCutElim', 'vacuousElim',
      'iteration', 'deiteration', 'conversion', 'relUnfold',
    ])
    expect(wire).toBeTruthy()
    expect(justifierRegion).toBeTruthy()
  })

  it('routes named/construction instantiation and exact relation folding', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const body = builder.termNode(builder.root, parseTerm('\\x. x'))
    const ref = builder.ref(builder.root, 'R', 0)
    const diagram = builder.build()
    const bodyBuilder = new DiagramBuilder()
    bodyBuilder.termNode(bodyBuilder.root, parseTerm('\\x. x'))
    const relations = new Map([['R', mkDiagramWithBoundary(bodyBuilder.build(), [])]])
    const applied: ProofAction[] = []
    const opened: string[] = []
    const selected = { value: [] as { kind: 'node' | 'region' | 'wire'; id: string }[] }
    const controller = controllerFor(diagram, selected, applied, opened, relations)
    const bubbleSelection = mkSelection(diagram, { region: builder.root, regions: [bubble], nodes: [], wires: [] })
    const bodySelection = mkSelection(diagram, { region: builder.root, regions: [], nodes: [body], wires: [] })

    expect(controller.invokeAction(
      { kind: 'instantiate', label: '', needsInput: 'comprehension' }, bubbleSelection, { kind: 'construction' },
    )).toBe(true)
    expect(controller.invokeAction(
      { kind: 'instantiate', label: '', needsInput: 'comprehension' }, bubbleSelection, { kind: 'relation', name: 'R' },
    )).toBe(true)
    expect(controller.invokeAction(
      { kind: 'relFold', label: '', needsInput: 'relation' }, bodySelection, { kind: 'relation', name: 'R' },
    )).toBe(true)
    expect(opened).toEqual([bubble])
    expect(stepsFrom(applied).map((step) => step.rule)).toEqual(['comprehensionInstantiate', 'relFold'])
    expect(ref).toBeTruthy()
  })

  it('routes empty-space term, relation, and bound-predicate menu clicks into proof actions', () => {
    const builder = new DiagramBuilder()
    const bubble = builder.bubble(builder.root, 0)
    const diagram = builder.build()
    const relationBuilder = new DiagramBuilder()
    const context = extendRelations(EMPTY_PROOF_CONTEXT, [
      ['R', mkDiagramWithBoundary(relationBuilder.build(), [])],
    ])
    const document = new MenuDocument()
    const host = new MenuElement(document)
    const applied: ProofAction[] = []
    const engine = mkEngine(diagram, [])
    engine.regions.set(bubble, { center: { x: 0, y: 0 }, radius: 10, support: [] })
    const center = engine.regions.get(bubble)?.center
    if (center === undefined) throw new Error('bubble has no rendered engine geometry')
    const controller = new GameProofMoveController({
      host: host as unknown as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => engine,
      viewScale: () => 1,
      selection: () => [],
      setSelection: () => undefined,
      context: () => context,
      apply: (action) => { applied.push(action) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })
    const open = (): void => {
      expect(controller.contextMenu(pointerSample(null, center))).toBe(true)
    }

    open()
    clickMenuAction(host, 'Term…')
    const prompt = host.querySelector<MenuElement>('.curse-proof-prompt')
    const input = prompt?.querySelector<MenuElement>('input')
    if (input === null || input === undefined) throw new Error('term-spawn prompt has no input')
    input.value = '\\x. x'
    const submit = prompt?.children.find((child) => child.textContent === 'Apply')
    if (submit === undefined) throw new Error('term-spawn prompt has no Apply button')
    submit.dispatchEvent(new Event('click'))

    open()
    clickMenuAction(host, 'Relation R')
    open()
    clickMenuAction(host, `Bound predicate ${bubble}`)

    expect(stepsFrom(applied)).toEqual([
      { rule: 'closedTermIntro', region: bubble, term: parseTerm('\\x. x') },
      { rule: 'relationSpawn', region: bubble, defId: 'R', arity: 0 },
      { rule: 'boundRelationSpawn', region: bubble, binder: bubble, arity: 0 },
    ])
  })

  it('routes wire sever and anchored split menu clicks into proof actions', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const target = builder.bubble(negative, 1)
    const witness = builder.termNode(target, parseTerm('\\x. x'))
    const consumer = builder.termNode(target, parseTerm('x'))
    const witnessEndpoint = { node: witness, port: { kind: 'output' as const } }
    const consumerEndpoint = { node: consumer, port: { kind: 'freeVar' as const, name: 'x' } }
    const wire = builder.wire(negative, [witnessEndpoint, consumerEndpoint])
    const diagram = builder.build()
    const canonicalWitness = diagram.wires[wire]!.endpoints.find(({ node }) => node === witness)!
    const canonicalConsumer = diagram.wires[wire]!.endpoints.find(({ node }) => node === consumer)!
    const document = new MenuDocument()
    const host = new MenuElement(document)
    const applied: ProofAction[] = []
    const hit = { kind: 'wire' as const, id: wire }
    const controller = new GameProofMoveController({
      host: host as unknown as HTMLElement,
      active: () => true,
      diagram: () => diagram,
      engine: () => mkEngine(diagram, []),
      viewScale: () => 1,
      selection: () => [hit],
      setSelection: () => undefined,
      context: () => EMPTY_PROOF_CONTEXT,
      apply: (action) => { applied.push(action) },
      refuse: (message) => { throw new Error(message) },
      theme: () => DARK,
      fuel: () => 256,
      openConstruction: () => undefined,
    })
    const open = (): void => {
      expect(controller.contextMenu(pointerSample(hit))).toBe(true)
    }

    open()
    clickMenuAction(host, `Sever after ${witness}/${portKey(canonicalWitness.port)}`)
    open()
    clickMenuAction(host, `Split ${consumer}/${portKey(canonicalConsumer.port)} from ${witness}`)

    expect(stepsFrom(applied)).toEqual([
      { rule: 'wireSever', wire, keep: [canonicalWitness] },
      {
        rule: 'anchoredWireSplit', wire, witness,
        endpoints: [canonicalConsumer], target,
      },
    ])
  })

  it('routes actual F and double-click fusion once each', () => {
    const builder = new DiagramBuilder()
    const term = builder.termNode(builder.root, parseTerm('x'))
    const diagram = builder.build()
    const wire = Object.keys(diagram.wires)[0]!
    const applied: ProofAction[] = []
    const selected = { value: [{ kind: 'wire' as const, id: wire }] }
    const controller = controllerFor(diagram, selected, applied, [])
    expect(controller.keyDown(key({ key: 'F' }))).toBe(true)
    selected.value = [{ kind: 'wire', id: wire }]
    expect(controller.doubleClick({
      pointerId: 1, button: 0, client: { x: 1, y: 1 }, screen: { x: 1, y: 1 },
      world: { x: 1, y: 1 }, hit: { kind: 'wire', id: wire },
      shiftKey: false, ctrlKey: false, altKey: false, metaKey: false,
    })).toBe(true)
    expect(stepsFrom(applied)).toEqual([{ rule: 'fusion', wire }, { rule: 'fusion', wire }])
    expect(term).toBeTruthy()
  })
})
