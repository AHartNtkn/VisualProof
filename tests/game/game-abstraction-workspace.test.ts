import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import type { ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyGameAction, currentDiagram, startPuzzle, type GameSession } from '../../src/game/session'
import { puzzleId } from '../../src/game/types'
import {
  createOccurrenceSetState,
  cycleOccurrenceSet,
  toggleOccurrenceExclusion,
  type AbstractionCandidate,
} from '../../src/interaction/abstraction-matches'
import {
  addRelationTerm,
  currentRelationDraft,
  insertOptionalPort,
} from '../../src/interaction/relation-workspace-draft'
import { AbstractTransaction } from '../../src/interaction/relation-transactions'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'

const authority = { context: EMPTY_PROOF_CONTEXT, artifact: () => undefined }

function scene() {
  const builder = new DiagramBuilder()
  const negative = builder.cut(builder.root)
  const first = builder.termNode(negative, parseTerm('\\x. x'))
  builder.wire(negative, [{ node: first, port: { kind: 'output' } }])
  const second = builder.termNode(negative, parseTerm('\\x. x'))
  builder.wire(negative, [{ node: second, port: { kind: 'output' } }])
  const diagram = builder.build()
  return {
    diagram,
    first,
    wrap: mkSelection(diagram, { region: negative, regions: [], nodes: [first, second], wires: [] }),
  }
}

function constructedPattern(transaction: AbstractTransaction) {
  let draft = addRelationTerm(transaction.initialDraft(), parseTerm('\\x. x'))
  const wire = Object.keys(currentRelationDraft(draft).diagram.wires)[0]!
  draft = insertOptionalPort(draft, wire, 0)
  return currentRelationDraft(draft)
}

function gameTransaction(options: {
  matcherFuel?: number
  solverFuel?: number
  apply?: (action: ProofAction) => void
  cancel?: () => void
} = {}) {
  const fixture = scene()
  let live = fixture.diagram
  const transaction = new AbstractTransaction({
    diagram: () => live,
    boundary: () => [],
    wrap: fixture.wrap,
    context: () => EMPTY_PROOF_CONTEXT,
    orientation: 'backward',
    apply: options.apply ?? (() => {}),
    cancel: options.cancel ?? (() => {}),
    engine: () => mkEngine(live, []),
    theme: () => DARK,
    matcherFuel: () => options.matcherFuel ?? 128,
    solverFuel: () => options.solverFuel ?? 1024,
  })
  return { fixture, transaction, setLive: (diagram: typeof live) => { live = diagram } }
}

function candidate(key: string, nodes: string[]): AbstractionCandidate {
  return {
    key,
    occurrence: { sel: { region: 'r0', regions: [], nodes: [], wires: [] }, args: [] },
    footprint: { nodes: new Set(nodes), wires: new Set(), regions: new Set() },
  }
}

describe('game live abstraction workspace', () => {
  it('constructs exact candidates, filters the submitted set, and records one accepted game action', () => {
    const fixture = scene()
    let session: GameSession = startPuzzle({ id: puzzleId('live-abstraction'), diagram: fixture.diagram })
    const source = JSON.stringify(fixture.diagram)
    const actions: ProofAction[] = []
    let live = fixture.diagram
    const transaction = new AbstractTransaction({
      diagram: () => live,
      boundary: () => [],
      wrap: fixture.wrap,
      context: () => EMPTY_PROOF_CONTEXT,
      orientation: 'backward',
      apply: (action) => {
        actions.push(action)
        session = applyGameAction(session, action, authority).session
        live = currentDiagram(session)
      },
      cancel: () => {},
      engine: () => mkEngine(live, []),
      theme: () => DARK,
      matcherFuel: () => 128,
      solverFuel: () => 1024,
    })
    const pattern = constructedPattern(transaction)

    transaction.draftChanged(pattern)
    expect(transaction.debugState()).toMatchObject({ candidateCount: 2, activeKeys: expect.any(Array) })
    const omitted = transaction.debugState().candidateKeys[0]!
    transaction.toggleExclusion(omitted)
    expect(transaction.debugState()).toMatchObject({ excludedKeys: [omitted], activeKeys: [expect.any(String)] })
    transaction.toggleExclusion(omitted)
    expect(transaction.debugState().activeKeys).toHaveLength(2)
    transaction.toggleExclusion(omitted)
    transaction.finalize(pattern, [])

    expect(actions).toHaveLength(1)
    expect(actions[0]!.steps).toEqual([expect.objectContaining({
      rule: 'comprehensionAbstract',
      wrap: fixture.wrap,
      occurrences: [expect.any(Object)],
    })])
    expect(session.timeline.actions).toHaveLength(1)
    expect(session.timeline.states).toHaveLength(2)
    expect(session.timeline.cursor).toBe(1)
    expect(JSON.stringify(fixture.diagram)).toBe(source)
    expect(currentDiagram(session)).not.toBe(fixture.diagram)
  })

  it('cycles forward and backward through compatible maximal occurrence sets', () => {
    const a = candidate('a', ['left'])
    const b = candidate('b', ['left', 'right'])
    const c = candidate('c', ['right'])
    const initial = createOccurrenceSetState([a, b, c], new Set(), 100)

    expect(initial.sets.map((set) => set.map(({ key }) => key))).toEqual([['a', 'c'], ['b']])
    expect(cycleOccurrenceSet(initial, 1).activeIndex).toBe(1)
    expect(cycleOccurrenceSet(initial, -1).activeIndex).toBe(1)
    expect(toggleOccurrenceExclusion(initial, 'b').sets[0]!.map(({ key }) => key)).toEqual(['a', 'c'])
  })

  it('cancels without changing the diagram or game action timeline', () => {
    let cancelled = 0
    const { fixture, transaction } = gameTransaction({ cancel: () => { cancelled++ } })
    const session = startPuzzle({ id: puzzleId('cancel-abstraction'), diagram: fixture.diagram })
    const pattern = constructedPattern(transaction)

    transaction.draftChanged(pattern)
    transaction.cancel()

    expect(cancelled).toBe(1)
    expect(session.timeline.actions).toEqual([])
    expect(session.timeline.states).toEqual([fixture.diagram])
    expect(session.timeline.cursor).toBe(0)
  })

  it('keeps stale-source and matcher/solver exhaustion as explicit refusals', () => {
    const stale = gameTransaction()
    const stalePattern = constructedPattern(stale.transaction)
    stale.transaction.draftChanged(stalePattern)
    stale.setLive(mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } }))
    expect(() => stale.transaction.finalize(stalePattern, [])).toThrow(/source changed|missing/i)

    const matcher = gameTransaction({ matcherFuel: 1 })
    const matcherPattern = constructedPattern(matcher.transaction)
    expect(matcher.transaction.status(matcherPattern)).toMatchObject({
      kind: 'refused', code: 'matcher-exhausted',
    })

    const solver = gameTransaction({ solverFuel: 1 })
    const solverPattern = constructedPattern(solver.transaction)
    expect(solver.transaction.status(solverPattern)).toMatchObject({
      kind: 'refused', code: 'solver-exhausted',
    })
  })
})
