import { describe, expect, it } from 'vitest'
import { GameDomainError, puzzleId } from '../../src/game/types'
import { applyGameStep, currentDiagram, moveCursor, startPuzzle } from '../../src/game/session'
import { isBlank } from '../../src/game/blank'
import { minimalPuzzle } from './catalog-fixture'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle = minimalPuzzle({
  id: puzzleId('four-veils'), name: { professional: 'Four Veils' }, goal: fixture.goal,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
})
const authority = {
  context: { relations: new Map(), theorems: new Map() },
}

describe('backward game session', () => {
  it('accepts positive-region insertion only in backward orientation', () => {
    const step = {
      rule: 'insertion' as const,
      region: puzzle.goal.diagram.root,
      pattern: puzzle.goal,
      attachments: [],
      binders: {},
    }

    const transition = applyGameStep(startPuzzle(puzzle), step, authority)

    expect(transition.session.timeline.steps).toEqual([step])
    expect(currentDiagram(transition.session)).not.toBe(puzzle.goal.diagram)
  })

  it('completes on canonical blank', () => {
    const start = startPuzzle(puzzle)
    const first = applyGameStep(start, puzzle.witness[0]!, authority)
    expect(first.completedNow).toBe(false)
    const second = applyGameStep(first.session, puzzle.witness[1]!, authority)
    expect(second.completedNow).toBe(true)
    expect(isBlank(currentDiagram(second.session))).toBe(true)
  })

  it('rejects every move from canonical blank', () => {
    const first = applyGameStep(startPuzzle(puzzle), puzzle.witness[0]!, authority).session
    const solved = applyGameStep(first, puzzle.witness[1]!, authority).session
    const blank = currentDiagram(solved)

    expect(() => applyGameStep(solved, {
      rule: 'doubleCutIntro',
      sel: { region: blank.root, regions: [], nodes: [], wires: [] },
    }, authority)).toThrow(GameDomainError)
    expect(solved.timeline.states).toHaveLength(3)
    expect(solved.timeline.steps).toHaveLength(2)
  })

  it('retains future while scrubbing and truncates it on a new continuation', () => {
    const first = applyGameStep(startPuzzle(puzzle), puzzle.witness[0]!, authority).session
    const solved = applyGameStep(first, puzzle.witness[1]!, authority).session
    const rewound = moveCursor(solved, 0)
    expect(rewound.timeline.states).toHaveLength(3)
    const branched = applyGameStep(rewound, puzzle.witness[0]!, authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.steps).toHaveLength(1)
    expect(branched.timeline.cursor).toBe(1)
  })

  it('fails atomically when a general theorem reference is unavailable in game content', () => {
    const start = startPuzzle(puzzle)
    expect(() => applyGameStep(start, {
      rule: 'theorem', name: 'unavailable', direction: 'forward',
      at: { sel: { region: puzzle.goal.diagram.root, regions: [], nodes: [], wires: [] }, args: [] },
    }, authority)).toThrow(/unknown theorem/)
    expect(currentDiagram(start)).toBe(puzzle.goal.diagram)
  })
})
