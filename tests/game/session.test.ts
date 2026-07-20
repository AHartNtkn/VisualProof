import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { GameDomainError, puzzleId } from '../../src/game/types'
import { applyGameSteps, currentDiagram, moveCursor, startPuzzle } from '../../src/game/session'
import { isBlank } from '../../src/game/blank'
import { minimalPuzzle } from './catalog-fixture'
import { fourVeils } from './fixtures'

const fixture = fourVeils()
const puzzle = minimalPuzzle({
  id: puzzleId('four-veils'), name: { professional: 'Four Veils' }, goal: fixture.goal,
  witness: fixture.eliminations.map((region) => ({ rule: 'doubleCutElim' as const, region })),
})
const corePuzzle = { id: puzzle.id, diagram: puzzle.goal.diagram }
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

    const transition = applyGameSteps(startPuzzle(corePuzzle), [step], authority)

    expect(transition.session.timeline.steps).toEqual([step])
    expect(currentDiagram(transition.session)).not.toBe(puzzle.goal.diagram)
  })

  it('completes on canonical blank', () => {
    const start = startPuzzle(corePuzzle)
    const first = applyGameSteps(start, [puzzle.witness[0]!], authority)
    expect(first.completedNow).toBe(false)
    const second = applyGameSteps(first.session, [puzzle.witness[1]!], authority)
    expect(second.completedNow).toBe(true)
    expect(isBlank(currentDiagram(second.session))).toBe(true)
  })

  it('rejects every move from canonical blank', () => {
    const first = applyGameSteps(startPuzzle(corePuzzle), [puzzle.witness[0]!], authority).session
    const solved = applyGameSteps(first, [puzzle.witness[1]!], authority).session
    const blank = currentDiagram(solved)

    expect(() => applyGameSteps(solved, [{
      rule: 'doubleCutIntro',
      sel: { region: blank.root, regions: [], nodes: [], wires: [] },
    }], authority)).toThrow(GameDomainError)
    expect(solved.timeline.states).toHaveLength(3)
    expect(solved.timeline.steps).toHaveLength(2)
  })

  it('retains future while scrubbing and truncates it on a new continuation', () => {
    const first = applyGameSteps(startPuzzle(corePuzzle), [puzzle.witness[0]!], authority).session
    const solved = applyGameSteps(first, [puzzle.witness[1]!], authority).session
    const rewound = moveCursor(solved, 0)
    expect(rewound.timeline.states).toHaveLength(3)
    const branched = applyGameSteps(rewound, [puzzle.witness[0]!], authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.steps).toHaveLength(1)
    expect(branched.timeline.cursor).toBe(1)
  })

  it('fails atomically when a general theorem reference is unavailable in game content', () => {
    const start = startPuzzle(corePuzzle)
    expect(() => applyGameSteps(start, [{
      rule: 'theorem', name: 'unavailable', direction: 'forward',
      at: { sel: { region: puzzle.goal.diagram.root, regions: [], nodes: [], wires: [] }, args: [] },
    }], authority)).toThrow(/unknown theorem/)
    expect(currentDiagram(start)).toBe(puzzle.goal.diagram)
  })

  it('applies a prepared batch as ordinary timeline steps and reports completion from the final step', () => {
    const transition = applyGameSteps(
      startPuzzle(corePuzzle),
      [puzzle.witness[0]!, ...puzzle.witness.slice(1)],
      authority,
    )

    expect(transition.completedNow).toBe(true)
    expect(transition.session.timeline.steps).toEqual(puzzle.witness)
    expect(transition.session.timeline.states).toHaveLength(puzzle.witness.length + 1)
    expect(transition.session.timeline.cursor).toBe(puzzle.witness.length)
  })

  it('preflights an entire batch before atomically replacing a rewound future', () => {
    const solved = applyGameSteps(
      startPuzzle(corePuzzle),
      [puzzle.witness[0]!, ...puzzle.witness.slice(1)],
      authority,
    ).session
    const rewound = moveCursor(solved, 0)
    const before = rewound.timeline
    const forged = { rule: 'doubleCutElim' as const, region: 'forged-region' }

    expect(() => applyGameSteps(rewound, [puzzle.witness[0]!, forged], authority)).toThrow()
    expect(rewound.timeline).toBe(before)

    const branched = applyGameSteps(rewound, [puzzle.witness[0]!], authority).session
    expect(branched.timeline.states).toHaveLength(2)
    expect(branched.timeline.steps).toEqual([puzzle.witness[0]])
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
    const fullFuture = applyGameSteps(startPuzzle(sixVeilPuzzle), threeSteps, authority).session
    const rewound = moveCursor(fullFuture, 0)

    const branched = applyGameSteps(rewound, [threeSteps[0], threeSteps[1]], authority).session
    expect(isBlank(currentDiagram(branched))).toBe(false)
    expect(branched.timeline.states).toHaveLength(3)
    expect(branched.timeline.steps).toEqual([threeSteps[0], threeSteps[1]])
    expect(branched.timeline.cursor).toBe(2)

    const oneBack = moveCursor(branched, 1)
    expect(currentDiagram(oneBack)).toBe(branched.timeline.states[1])
    const twoBack = moveCursor(oneBack, 0)
    expect(currentDiagram(twoBack)).toBe(branched.timeline.states[0])
    const oneForward = moveCursor(twoBack, 1)
    expect(currentDiagram(oneForward)).toBe(branched.timeline.states[1])
    const twoForward = moveCursor(oneForward, 2)
    expect(currentDiagram(twoForward)).toBe(branched.timeline.states[2])
  })
})
