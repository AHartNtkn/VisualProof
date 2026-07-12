import { describe, expect, it } from 'vitest'
import {
  applyGameStep,
  currentDiagram,
  startPuzzle,
  teacherInterventionsFor,
  type GameRuntimeAuthority,
  type TeacherIntervention,
  type TeacherSignal,
} from '../../src/game'
import { fixturePerformanceId, minimalPuzzle } from './catalog-fixture'
import { fourVeils, twoVeils } from './fixtures'

const four = fourVeils()
const opening: TeacherIntervention = {
  id: 'opening-four',
  performance: fixturePerformanceId,
  trigger: { kind: 'opening' },
  text: 'Begin with the innermost pair.',
  repeat: 'once',
}
const reachedTwoVeils: TeacherIntervention = {
  id: 'inner-pair-removed',
  performance: fixturePerformanceId,
  trigger: {
    kind: 'proofState',
    state: twoVeils().goal,
    demonstration: [{ rule: 'doubleCutElim', region: four.eliminations[0]! }],
  },
  text: 'That route leaves the older paired form.',
  repeat: 'once',
  recovery: 'timeline',
}
const stalledTwo: TeacherIntervention = {
  id: 'stalled-two',
  trigger: { kind: 'stalled', level: 2 },
  text: 'Use the timeline to compare the two forms.',
  repeat: 'repeatable',
}
const completion: TeacherIntervention = {
  id: 'completion',
  trigger: { kind: 'completion' },
  text: 'The form is clear.',
  repeat: 'once',
}
const puzzle = minimalPuzzle({
  goal: four.goal,
  witness: [
    { rule: 'doubleCutElim', region: four.eliminations[0]! },
    { rule: 'doubleCutElim', region: four.eliminations[1]! },
  ],
  teacher: [opening, reachedTwoVeils, stalledTwo, completion],
})
const authority: GameRuntimeAuthority = {
  context: { relations: new Map() },
  puzzle: () => puzzle,
  canUseVellum: () => false,
}

describe('teacher interventions', () => {
  it('matches opening and suppresses a seen once-only intervention', () => {
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set()))
      .toEqual([opening])
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set([opening.id])))
      .toEqual([])
  })

  it('matches a committed diagram by canonical proof state', () => {
    const transition = applyGameStep(
      startPuzzle(puzzle),
      { rule: 'doubleCutElim', region: four.eliminations[0]! },
      authority,
    )

    expect(teacherInterventionsFor(
      puzzle,
      { kind: 'proofState', diagram: currentDiagram(transition.session) },
      new Set(),
    )).toEqual([reachedTwoVeils])
    expect(teacherInterventionsFor(
      puzzle,
      { kind: 'proofState', diagram: four.goal.diagram },
      new Set(),
    )).toEqual([])
  })

  it('matches stalled levels and completion only to their exact signal kinds', () => {
    expect(teacherInterventionsFor(puzzle, { kind: 'stalled', level: 1 }, new Set()))
      .toEqual([])
    expect(teacherInterventionsFor(puzzle, { kind: 'stalled', level: 2 }, new Set()))
      .toEqual([stalledTwo])
    expect(teacherInterventionsFor(puzzle, { kind: 'completion' }, new Set()))
      .toEqual([completion])
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set()))
      .not.toContain(completion)
  })

  it('keeps a seen repeatable intervention available', () => {
    expect(teacherInterventionsFor(
      puzzle,
      { kind: 'stalled', level: 2 },
      new Set([stalledTwo.id]),
    )).toEqual([stalledTwo])
  })

  it('leaves invalid-step refusal outside the teacher signal path', () => {
    const unchanged = startPuzzle(puzzle)
    const before = currentDiagram(unchanged)
    let signal: TeacherSignal | undefined

    expect(() => {
      const transition = applyGameStep(
        unchanged,
        { rule: 'doubleCutElim', region: 'missing-region' },
        authority,
      )
      signal = { kind: 'proofState', diagram: currentDiagram(transition.session) }
    }).toThrow()
    expect(currentDiagram(unchanged)).toBe(before)
    expect(signal).toBeUndefined()
  })
})
