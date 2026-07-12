import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import {
  applyForward,
  applyBackward,
  applyTrack,
  assembleTheorem,
  currentSide,
  currentTrack,
  declareTrack,
  meet,
  moveSide,
  moveTrack,
  redoForward,
  redoBackward,
  redoTrack,
  startSession,
  startTrack,
  undoForward,
  undoBackward,
  undoTrack,
  timelineActiveSteps,
} from '../../src/app/session'

const ctx = verifyTheory(buildFregeTheory())

function bare() {
  const b = new DiagramBuilder()
  b.termNode(b.root, parseTerm('\\x. x'))
  return mkDiagramWithBoundary(b.build(), [])
}

function intro(diagram = bare().diagram) {
  return {
    rule: 'doubleCutIntro' as const,
    sel: mkSelection(diagram, { region: diagram.root, regions: [], nodes: [], wires: [] }),
  }
}

describe('authoritative proof timeline', () => {
  it('starts with one state and moves undo/redo without deleting the future', () => {
    const s0 = startTrack(bare(), 'forward', ctx)
    expect(s0.timeline).toEqual({ states: [s0.origin.diagram], transitions: [], cursor: 0 })

    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const undone = undoTrack(s1)
    expect(undone.timeline.states).toBe(s1.timeline.states)
    expect(undone.timeline.transitions).toBe(s1.timeline.transitions)
    expect(timelineActiveSteps(undone.timeline)).toEqual([])
    expect(undone.timeline.cursor).toBe(0)
    expect(currentTrack(undone)).toBe(s0.origin.diagram)
    const redone = redoTrack(undone)
    expect(redone.timeline.cursor).toBe(1)
    expect(currentTrack(redone)).toBe(currentTrack(s1))
    expect(timelineActiveSteps(redone.timeline)).toEqual(redone.timeline.transitions)
  })

  it('moves to any retained state and truncates future when applying there', () => {
    const s0 = startTrack(bare(), 'forward', ctx)
    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const s2 = applyTrack(s1, intro(currentTrack(s1)))
    const rewound = moveTrack(s2, 0)
    const replacementStep = {
      rule: 'vacuousIntro' as const,
      sel: mkSelection(currentTrack(rewound), { region: currentTrack(rewound).root, regions: [], nodes: [], wires: [] }),
      arity: 0,
    }
    const replacement = applyTrack(rewound, replacementStep)

    expect(s2.timeline).toMatchObject({ cursor: 2 })
    expect(rewound.timeline.states).toHaveLength(3)
    expect(replacement.timeline.states).toHaveLength(2)
    expect(replacement.timeline.transitions).toHaveLength(1)
    expect(replacement.timeline.transitions).toEqual([replacementStep])
    expect(replacement.timeline.cursor).toBe(1)
    expect(() => redoTrack(replacement)).toThrow(/nothing to redo/)
  })

  it('declares only the cursor state and step prefix', () => {
    const s0 = startTrack(bare(), 'forward', ctx)
    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const s2 = applyTrack(s1, intro(currentTrack(s1)))
    const rewound = moveTrack(s2, 1)
    const theorem = declareTrack(rewound, 'prefix')

    expect(theorem.rhs.diagram).toBe(s1.timeline.states[1])
    expect(theorem.steps).toEqual(timelineActiveSteps(rewound.timeline))
  })

  it('keeps fixed-side cursors independent and meets/assembles at those cursors', () => {
    const lhs = bare()
    const builder = new DiagramBuilder()
    builder.termNode(builder.root, parseTerm('\\x. x'))
    const outer = builder.cut(builder.root)
    builder.cut(outer)
    const rhs = mkDiagramWithBoundary(builder.build(), [])
    const s0 = startSession(lhs, rhs, ctx)
    const s1 = applyForward(s0, intro(currentSide(s0, 'forward')))
    const undone = undoForward(s1)

    expect(undone.forward.cursor).toBe(0)
    expect(undone.backward.cursor).toBe(0)
    expect(undone.forward.states).toHaveLength(2)
    expect(meet(undone)).toBe(false)
    expect(meet(redoForward(undone))).toBe(true)
    expect(moveSide(s1, 'backward', 0).forward.cursor).toBe(1)
    expect(assembleTheorem(s1, 'fixed-prefix').steps).toEqual(timelineActiveSteps(s1.forward))
  })

  it('replaces an abandoned backward transition and leaves no redo tail', () => {
    const side = bare()
    const s0 = startSession(side, side, ctx)
    const first = {
      rule: 'vacuousIntro' as const,
      sel: mkSelection(currentSide(s0, 'backward'), { region: currentSide(s0, 'backward').root, regions: [], nodes: [], wires: [] }),
      arity: 0,
    }
    const s1 = applyBackward(s0, first)
    const abandoned = intro(currentSide(s1, 'backward'))
    const s2 = applyBackward(s1, abandoned)
    const rewound = undoBackward(s2)
    expect(timelineActiveSteps(rewound.backward)).toEqual([first])
    expect(timelineActiveSteps(redoBackward(rewound).backward)).toEqual([first, abandoned])

    const replacement = {
      rule: 'vacuousIntro' as const,
      sel: mkSelection(currentSide(rewound, 'backward'), { region: currentSide(rewound, 'backward').root, regions: [], nodes: [], wires: [] }),
      arity: 1,
    }
    const diverged = applyBackward(rewound, replacement)

    expect(diverged.backward.transitions).toEqual([first, replacement])
    expect(timelineActiveSteps(diverged.backward)).toEqual([first, replacement])
    expect(() => redoBackward(diverged)).toThrow(/nothing to redo/)
  })
})
