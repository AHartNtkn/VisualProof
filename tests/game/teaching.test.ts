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
const recognizedUnwinnable: TeacherIntervention = {
  id: 'empty-veil-trap',
  performance: fixturePerformanceId,
  trigger: {
    kind: 'recognizedUnwinnable',
    state: twoVeils().goal,
    demonstration: [{ rule: 'doubleCutElim', region: four.eliminations[0]! }],
  },
  text: 'That route cannot reach blank. Return on the timeline.',
  repeat: 'once',
  recovery: 'timeline',
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
  teacher: [opening, recognizedUnwinnable, completion],
})
const authority: GameRuntimeAuthority = {
  context: { relations: new Map(), theorems: new Map() },
}

describe('teacher presentations', () => {
  it('offers opening mechanic instruction as a modal and suppresses it once seen', () => {
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set()))
      .toEqual([{ intervention: opening, presentation: { kind: 'modalInstruction' } }])
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set([opening.id])))
      .toEqual([])
  })

  it('offers an exact authored unwinnable state as nonblocking timeline-recovery commentary', () => {
    const transition = applyGameStep(
      startPuzzle(puzzle),
      { rule: 'doubleCutElim', region: four.eliminations[0]! },
      authority,
    )

    expect(teacherInterventionsFor(
      puzzle,
      { kind: 'recognizedUnwinnable', diagram: currentDiagram(transition.session) },
      new Set(),
    )).toEqual([{
      intervention: recognizedUnwinnable,
      presentation: { kind: 'nonblockingCommentary', recovery: 'timeline' },
    }])
    expect(teacherInterventionsFor(
      puzzle,
      { kind: 'recognizedUnwinnable', diagram: four.goal.diagram },
      new Set(),
    )).toEqual([])
  })

  it('offers completion through completion-owned commentary only', () => {
    expect(teacherInterventionsFor(puzzle, { kind: 'completion' }, new Set()))
      .toEqual([{
        intervention: completion,
        presentation: { kind: 'completionCommentary' },
      }])
    expect(teacherInterventionsFor(puzzle, { kind: 'opening' }, new Set()))
      .not.toContainEqual(expect.objectContaining({ intervention: completion }))
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
      signal = {
        kind: 'recognizedUnwinnable',
        diagram: currentDiagram(transition.session),
      }
    }).toThrow()
    expect(currentDiagram(unchanged)).toBe(before)
    expect(signal).toBeUndefined()
  })
})
