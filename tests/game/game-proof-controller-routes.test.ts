import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection, type SubgraphSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import {
  GameProofMoveController,
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
  apply: (step) => { applied.push(step) },
  refuse: (message) => { throw new Error(message) },
  theme: () => DARK,
  fuel: () => 256,
  openConstruction: (bubble) => { opened.push(bubble) },
})

describe('actual game proof controller routes', () => {
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
