import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { GameDomainError, puzzleId } from '../../src/game/types'
import { applyGameAction, currentDiagram, moveCursor, startPuzzle } from '../../src/game/session'
import { isBlank } from '../../src/game/blank'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import type { ProofAction } from '../../src/kernel/proof/action'
import { singleStepAction } from '../../src/kernel/proof/action'
import type { ProofStep } from '../../src/kernel/proof/step'
import { parseTerm } from '../../src/kernel/term/parse'
import { freePorts } from '../../src/kernel/term/term'
import { minimalPuzzle } from './catalog-fixture'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle = minimalPuzzle({
  id: puzzleId('four-veils'), name: { professional: 'Four Veils' }, goal: fixture.goal,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
})
const corePuzzle = { id: puzzle.id, diagram: puzzle.goal.diagram }
const authority = {
  context: EMPTY_PROOF_CONTEXT,
}
const gesture = (step: ProofStep): ProofAction => singleStepAction(step.rule, step)
const compound = (label: string, steps: readonly ProofStep[]): ProofAction => ({
  label,
  steps,
  placements: [],
})

describe('backward game session', () => {
  it('records a compound user gesture as one action, one state, and one move', () => {
    const action: ProofAction = {
      label: 'remove both veil pairs',
      steps: puzzle.witness.map((step) => ({ ...step })),
      placements: [],
    }

    const transition = applyGameAction(startPuzzle(corePuzzle), action, authority)

    expect(transition.completedNow).toBe(true)
    expect(transition.session.timeline.actions).toEqual([action])
    expect(transition.session.timeline.states).toHaveLength(2)
    expect(transition.session.timeline.cursor).toBe(1)
  })

  it('owns a codec-normalized action snapshot instead of retaining caller-mutable proof data', () => {
    const expectedFirst = { ...puzzle.witness[0]! }
    const supplied = {
      label: 'remove both veil pairs',
      steps: puzzle.witness.map((step) => ({ ...step })),
      placements: [],
      allocation: { regions: [], nodes: ['reserved-node'], wires: [] },
    } as ProofAction as unknown as {
      label: string
      steps: Array<{ rule: 'doubleCutElim'; region: string }>
      placements: Array<{ introducedNode: number; x: number; y: number }>
      allocation: { regions: string[]; nodes: string[]; wires: string[] }
    }
    const transition = applyGameAction(startPuzzle(corePuzzle), supplied, authority)
    const retained = transition.session.timeline.actions[0]!

    supplied.label = 'mutated'
    supplied.steps[0]!.region = 'forged-region'
    supplied.placements.push({ introducedNode: 0, x: 1, y: 2 })
    supplied.allocation.nodes.push('later-reservation')

    expect(retained).not.toBe(supplied)
    expect(retained.label).toBe('remove both veil pairs')
    expect(retained.steps[0]).toEqual(expectedFirst)
    expect(retained.placements).toEqual([])
    expect(retained.allocation?.nodes).toEqual(['reserved-node'])
  })

  it('accepts positive-region atomic spawning only in backward orientation', () => {
    const term = parseTerm('x')
    const step = {
      rule: 'openTermSpawn' as const,
      region: puzzle.goal.diagram.root,
      term,
      freePorts: freePorts(term),
    }

    const transition = applyGameAction(startPuzzle(corePuzzle), gesture(step), authority)

    expect(transition.session.timeline.actions).toEqual([gesture(step)])
    expect(currentDiagram(transition.session)).not.toBe(puzzle.goal.diagram)
  })

  it('completes on canonical blank', () => {
    const start = startPuzzle(corePuzzle)
    const first = applyGameAction(start, gesture(puzzle.witness[0]!), authority)
    expect(first.completedNow).toBe(false)
    const second = applyGameAction(first.session, gesture(puzzle.witness[1]!), authority)
    expect(second.completedNow).toBe(true)
    expect(isBlank(currentDiagram(second.session))).toBe(true)
  })

  it('rejects every move from canonical blank', () => {
    const first = applyGameAction(startPuzzle(corePuzzle), gesture(puzzle.witness[0]!), authority).session
    const solved = applyGameAction(first, gesture(puzzle.witness[1]!), authority).session
    const blank = currentDiagram(solved)

    expect(() => applyGameAction(solved, gesture({
      rule: 'doubleCutIntro',
      sel: { region: blank.root, regions: [], nodes: [], wires: [] },
    }), authority)).toThrow(GameDomainError)
    expect(solved.timeline.states).toHaveLength(3)
    expect(solved.timeline.actions).toHaveLength(2)
  })

  it('retains future while scrubbing and truncates it on a new continuation', () => {
    const first = applyGameAction(startPuzzle(corePuzzle), gesture(puzzle.witness[0]!), authority).session
    const solved = applyGameAction(first, gesture(puzzle.witness[1]!), authority).session
    const rewound = moveCursor(solved, 0)
    expect(rewound.timeline.states).toHaveLength(3)
    const branched = applyGameAction(rewound, gesture(puzzle.witness[0]!), authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.actions).toHaveLength(1)
    expect(branched.timeline.cursor).toBe(1)
  })

  it('fails atomically when a general theorem reference is unavailable in game content', () => {
    const start = startPuzzle(corePuzzle)
    expect(() => applyGameAction(start, gesture({
      rule: 'theorem', name: 'unavailable', direction: 'forward',
      at: { sel: { region: puzzle.goal.diagram.root, regions: [], nodes: [], wires: [] }, args: [] },
    }), authority)).toThrow(/unknown theorem/)
    expect(currentDiagram(start)).toBe(puzzle.goal.diagram)
  })

  it('applies a prepared compound action atomically and reports completion from its final step', () => {
    const action = compound('remove all veils', puzzle.witness)
    const transition = applyGameAction(
      startPuzzle(corePuzzle),
      action,
      authority,
    )

    expect(transition.completedNow).toBe(true)
    expect(transition.session.timeline.actions).toEqual([action])
    expect(transition.session.timeline.states).toHaveLength(2)
    expect(transition.session.timeline.cursor).toBe(1)
  })

  it('preflights an entire batch before atomically replacing a rewound future', () => {
    const solved = applyGameAction(
      startPuzzle(corePuzzle),
      compound('solve', puzzle.witness),
      authority,
    ).session
    const rewound = moveCursor(solved, 0)
    const before = rewound.timeline
    const forged = { rule: 'doubleCutElim' as const, region: 'forged-region' }

    expect(() => applyGameAction(rewound, compound('forged', [puzzle.witness[0]!, forged]), authority)).toThrow()
    expect(rewound.timeline).toBe(before)

    const branched = applyGameAction(rewound, gesture(puzzle.witness[0]!), authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.actions).toEqual([gesture(puzzle.witness[0]!)])
    expect(branched.timeline.cursor).toBe(1)
  })

  it('replaces a rewound future once with a non-completing batch and traverses each appended operation', () => {
    const builder = new DiagramBuilder()
    const cuts: string[] = []
    let parent = builder.root
    for (let index = 0; index < 6; index++) {
      parent = builder.cut(parent)
      cuts.push(parent)
    }
    const sixVeilPuzzle = { id: puzzleId('six-veils'), diagram: builder.build() }
    const threeSteps = [
      { rule: 'doubleCutElim' as const, region: cuts[4]! },
      { rule: 'doubleCutElim' as const, region: cuts[2]! },
      { rule: 'doubleCutElim' as const, region: cuts[0]! },
    ] as const
    const fullFuture = applyGameAction(startPuzzle(sixVeilPuzzle), compound('three operations', threeSteps), authority).session
    const rewound = moveCursor(fullFuture, 0)

    const branchAction = compound('two operations', [threeSteps[0], threeSteps[1]])
    const branched = applyGameAction(rewound, branchAction, authority).session
    expect(isBlank(currentDiagram(branched))).toBe(false)
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.actions).toEqual([branchAction])
    expect(branched.timeline.cursor).toBe(1)

    const beforeAction = moveCursor(branched, 0)
    expect(currentDiagram(beforeAction)).toBe(branched.timeline.states[0])
    const afterAction = moveCursor(beforeAction, 1)
    expect(currentDiagram(afterAction)).toBe(branched.timeline.states[1])
  })
})
