import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { parseTerm } from '../../src/kernel/term/parse'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory } from '../../src/kernel/proof/store'
import {
  applyForward,
  applyTrack,
  assembleTheorem,
  currentSide,
  currentTrack,
  declareTrack,
  meet,
  moveSide,
  moveTrack,
  redoForward,
  redoTrack,
  startSession,
  startTrack,
  undoForward,
  undoTrack,
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
    expect(s0.timeline).toEqual({ states: [s0.origin.diagram], steps: [], cursor: 0 })

    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const undone = undoTrack(s1)
    expect(undone.timeline.states).toBe(s1.timeline.states)
    expect(undone.timeline.steps).toBe(s1.timeline.steps)
    expect(undone.timeline.cursor).toBe(0)
    expect(currentTrack(undone)).toBe(s0.origin.diagram)
    expect(redoTrack(undone).timeline.cursor).toBe(1)
  })

  it('moves to any retained state and truncates future when applying there', () => {
    const s0 = startTrack(bare(), 'forward', ctx)
    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const s2 = applyTrack(s1, intro(currentTrack(s1)))
    const rewound = moveTrack(s2, 0)
    const replacement = applyTrack(rewound, intro(currentTrack(rewound)))

    expect(s2.timeline).toMatchObject({ cursor: 2 })
    expect(rewound.timeline.states).toHaveLength(3)
    expect(replacement.timeline.states).toHaveLength(2)
    expect(replacement.timeline.steps).toHaveLength(1)
    expect(replacement.timeline.cursor).toBe(1)
  })

  it('declares only the cursor state and step prefix', () => {
    const s0 = startTrack(bare(), 'forward', ctx)
    const s1 = applyTrack(s0, intro(currentTrack(s0)))
    const s2 = applyTrack(s1, intro(currentTrack(s1)))
    const rewound = moveTrack(s2, 1)
    const theorem = declareTrack(rewound, 'prefix')

    expect(theorem.rhs.diagram).toBe(s1.timeline.states[1])
    expect(theorem.steps).toEqual(s2.timeline.steps.slice(0, 1))
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
    expect(assembleTheorem(s1, 'fixed-prefix').steps).toEqual(s1.forward.steps.slice(0, s1.forward.cursor))
  })
})
