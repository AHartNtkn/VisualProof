import { describe, expect, it } from 'vitest'
import { applyGameStep, currentDiagram, startPuzzle, type GameRuntimeAuthority } from '../../src/game/session'
import { guidanceInterventionsFor, type TeacherSignal } from '../../src/game/teaching'
import { guidanceDeliveryIdentity, type TeacherIntervention } from '../../src/game/types'
import { fixturePerformanceId, minimalPuzzle } from './catalog-fixture'
import { fourVeils, twoVeils } from './fixtures'

const four = fourVeils()
const opening: TeacherIntervention = {
  id: 'opening-four',
  performance: fixturePerformanceId,
  trigger: { kind: 'opening' },
  pages: ['Begin with the innermost pair.'],
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
  pages: ['That route cannot reach blank. Return on the timeline.'],
  repeat: 'once',
  recovery: 'timeline',
}
const completion: TeacherIntervention = {
  id: 'completion',
  trigger: { kind: 'completion' },
  pages: ['The form is clear.'],
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
const openingIdentity = guidanceDeliveryIdentity(puzzle.id, opening.id)
const recognizedIdentity = guidanceDeliveryIdentity(puzzle.id, recognizedUnwinnable.id)
const completionIdentity = guidanceDeliveryIdentity(puzzle.id, completion.id)

describe('passive guidance matching', () => {
  it('offers opening guidance and suppresses it once delivered', () => {
    expect(guidanceInterventionsFor(puzzle, { kind: 'opening' }, []))
      .toEqual([{
        identity: openingIdentity,
        intervention: opening,
      }])
    expect(guidanceInterventionsFor(puzzle, { kind: 'opening' }, [openingIdentity]))
      .toEqual([])
  })

  it('offers an exact authored unwinnable state as passive recovery guidance', () => {
    const transition = applyGameStep(
      startPuzzle(puzzle),
      { rule: 'doubleCutElim', region: four.eliminations[0]! },
      authority,
    )

    expect(guidanceInterventionsFor(
      puzzle,
      { kind: 'recognizedUnwinnable', diagram: currentDiagram(transition.session) },
      [],
    )).toEqual([{
      identity: recognizedIdentity,
      intervention: recognizedUnwinnable,
    }])
    expect(guidanceInterventionsFor(
      puzzle,
      { kind: 'recognizedUnwinnable', diagram: four.goal.diagram },
      [],
    )).toEqual([])
  })

  it('offers completion through completion-owned commentary only', () => {
    expect(guidanceInterventionsFor(puzzle, { kind: 'completion' }, []))
      .toEqual([{
        identity: completionIdentity,
        intervention: completion,
      }])
    expect(guidanceInterventionsFor(puzzle, { kind: 'opening' }, []))
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
