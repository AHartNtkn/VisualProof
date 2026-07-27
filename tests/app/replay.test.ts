import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyAction, singleStepAction } from '../../src/kernel/proof/action'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import { mkReplay } from '../../src/app/replay'
import { applyTrack, declareTrack, startTrack } from '../../src/app/session'
import { buildFregeTheory } from '../../src/theories/frege'
import { tinyTheory } from '../fixtures/zero-signature'

function replayFixture() {
  const diagram = new DiagramBuilder().build()
  const origin = mkDiagramWithBoundary(diagram, [])
  const selection = mkSelection(diagram, {
    region: diagram.root, regions: [], nodes: [], wires: [],
  })
  const base = verifyTheory(tinyTheory())
  const track = applyTrack(startTrack(origin, 'forward', base), singleStepAction('Double cut', {
    rule: 'doubleCutIntro',
    sel: selection,
  }))
  const theorem = declareTrack(track, 'DoubleNegation')
  return { ctx: registerTheorem(base, theorem), theorem }
}

function twoSidedFixture() {
  const lhsDiagram = new DiagramBuilder().build()
  const rhsDiagram = new DiagramBuilder().build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [])
  const rhs = mkDiagramWithBoundary(rhsDiagram, [])
  const forward = singleStepAction('open from lhs', {
    rule: 'doubleCutIntro',
    sel: mkSelection(lhsDiagram, {
      region: lhsDiagram.root, regions: [], nodes: [], wires: [],
    }),
  })
  const backward = singleStepAction('open from rhs', {
    rule: 'doubleCutIntro',
    sel: mkSelection(rhsDiagram, {
      region: rhsDiagram.root, regions: [], nodes: [], wires: [],
    }),
  })
  const theorem = {
    name: 'TwoSided',
    lhs,
    rhs,
    actions: [forward],
    backActions: [backward],
  }
  const base = verifyTheory(tinyTheory())
  const ctx = registerTheorem(base, theorem)
  return {
    ctx,
    theorem: ctx.theorems.get(theorem.name)!,
    meet: applyAction(lhsDiagram, forward, base, 'forward'),
  }
}

describe('structural replay', () => {
  it('exposes action labels, steps, diagrams, and transported boundaries', () => {
    const { ctx } = replayFixture()
    const replay = mkReplay('DoubleNegation', ctx)
    expect(replay.actionCount).toBe(1)
    expect(replay.labelAt(1)).toBe('forward · Double cut')
    expect(replay.stepsAt(1)[0]?.rule).toBe('doubleCutIntro')
    expect(Object.keys(replay.diagramAt(1).regions)).toHaveLength(3)
    expect(replay.boundaryAt(1)).toEqual([])
    expect(() => replay.diagramAt(2)).toThrow(/out of range/)
  })

  it('presents independently verified proof halves from exact lhs through meet to exact rhs', () => {
    const { ctx, theorem, meet } = twoSidedFixture()
    const replay = mkReplay(theorem.name, ctx)

    expect(replay.actionCount).toBe(2)
    expect(replay.meetingIndex).toBe(1)
    expect(replay.diagramAt(0)).toBe(theorem.lhs.diagram)
    expect(exploreForm(replay.diagramAt(0), replay.boundaryAt(0)))
      .toBe(exploreForm(theorem.lhs.diagram, theorem.lhs.boundary))
    expect(exploreForm(replay.diagramAt(replay.meetingIndex), replay.boundaryAt(replay.meetingIndex)))
      .toBe(exploreForm(meet))
    expect(replay.diagramAt(replay.actionCount)).toBe(theorem.rhs.diagram)
    expect(exploreForm(replay.diagramAt(replay.actionCount), replay.boundaryAt(replay.actionCount)))
      .toBe(exploreForm(theorem.rhs.diagram, theorem.rhs.boundary))

    expect(replay.labelAt(1)).toBe('forward · open from lhs')
    expect(replay.labelAt(2)).toBe('backward · open from rhs')
    expect(replay.transitions.map(({ half, orientation }) => ({ half, orientation })))
      .toEqual([
        { half: 'forward', orientation: 'forward' },
        { half: 'backward', orientation: 'backward' },
      ])
    expect(replay.transitions[1]!.action).toBe(theorem.backActions![0])
    expect(replay.transitions[1]!.appliedFrom).toBe(theorem.rhs.diagram)
  })

  it('ends zeroIsNat at its declared RHS with the folded nat reference visible', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const theorem = ctx.theorems.get('zeroIsNat')!
    const replay = mkReplay('zeroIsNat', ctx)
    const final = replay.diagramAt(replay.actionCount)

    expect(final).toBe(theorem.rhs.diagram)
    expect(exploreForm(final, replay.boundaryAt(replay.actionCount)))
      .toBe(exploreForm(theorem.rhs.diagram, theorem.rhs.boundary))
    expect(Object.values(final.nodes).some((node) =>
      node.kind === 'ref' && node.defId === 'nat')).toBe(true)
  })
})
