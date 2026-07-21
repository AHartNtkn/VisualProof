import { describe, expect, it } from 'vitest'
import { applyGameAction, currentDiagram, startPuzzle, type GameRuntimeAuthority } from '../../src/game/session'
import { guidanceInterventionsFor, type TeacherSignal } from '../../src/game/teaching'
import { guidanceDeliveryIdentity, puzzleId, type GuidanceDefinition, type GuidanceIntervention } from '../../src/game/types'
import { singleStepAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { fourVeils, twoVeils } from './fixtures'

const four = fourVeils()
const opening: GuidanceIntervention = {
  id: 'opening-four',
  trigger: { kind: 'opening' },
  pages: ['Begin with the innermost pair.'],
  repeat: 'once',
}
const recognizedUnwinnable: GuidanceIntervention = {
  id: 'empty-veil-trap',
  trigger: {
    kind: 'recognizedUnwinnable',
    state: twoVeils().goal,
  },
  pages: ['That route cannot reach blank. Return on the timeline.'],
  repeat: 'once',
  recovery: 'timeline',
}
const completion: GuidanceIntervention = {
  id: 'completion',
  trigger: { kind: 'completion' },
  pages: ['The form is clear.'],
  repeat: 'once',
}
const puzzle = { id: puzzleId('four-veils'), diagram: four.goal.diagram }
const guidance: GuidanceDefinition = {
  puzzle: puzzle.id,
  interventions: [opening, recognizedUnwinnable, completion],
}
const authority: GameRuntimeAuthority = {
  context: EMPTY_PROOF_CONTEXT,
  artifact: () => undefined,
}
const openingIdentity = guidanceDeliveryIdentity(puzzle.id, opening.id)
const recognizedIdentity = guidanceDeliveryIdentity(puzzle.id, recognizedUnwinnable.id)
const completionIdentity = guidanceDeliveryIdentity(puzzle.id, completion.id)

describe('passive guidance matching', () => {
  it('offers opening guidance and suppresses it once delivered', () => {
    expect(guidanceInterventionsFor(guidance, { kind: 'opening' }, []))
      .toEqual([{
        identity: openingIdentity,
        intervention: opening,
      }])
    expect(guidanceInterventionsFor(guidance, { kind: 'opening' }, [openingIdentity]))
      .toEqual([])
  })

  it('offers an exact authored unwinnable state as passive recovery guidance', () => {
    const transition = applyGameAction(
      startPuzzle(puzzle),
      singleStepAction('doubleCutElim', { rule: 'doubleCutElim', region: four.eliminations[0]! }),
      authority,
    )

    expect(guidanceInterventionsFor(
      guidance,
      { kind: 'recognizedUnwinnable', diagram: currentDiagram(transition.session) },
      [],
    )).toEqual([{
      identity: recognizedIdentity,
      intervention: recognizedUnwinnable,
    }])
    expect(guidanceInterventionsFor(
      guidance,
      { kind: 'recognizedUnwinnable', diagram: four.goal.diagram },
      [],
    )).toEqual([])
  })

  it('offers completion through completion-owned commentary only', () => {
    expect(guidanceInterventionsFor(guidance, { kind: 'completion' }, []))
      .toEqual([{
        identity: completionIdentity,
        intervention: completion,
      }])
    expect(guidanceInterventionsFor(guidance, { kind: 'opening' }, []))
      .not.toContainEqual(expect.objectContaining({ intervention: completion }))
  })

  it('leaves invalid-step refusal outside the teacher signal path', () => {
    const unchanged = startPuzzle(puzzle)
    const before = currentDiagram(unchanged)
    let signal: TeacherSignal | undefined

    expect(() => {
      const transition = applyGameAction(
        unchanged,
        singleStepAction('doubleCutElim', { rule: 'doubleCutElim', region: 'missing-region' }),
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
