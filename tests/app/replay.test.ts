import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { sameDiagram } from '../../src/kernel/diagram/canonical/iso'
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

function allForwardCanonicalFixture() {
  const lhsDiagram = new DiagramBuilder().build()
  const lhs = mkDiagramWithBoundary(lhsDiagram, [])
  const action = singleStepAction('open from lhs', {
    rule: 'doubleCutIntro',
    sel: mkSelection(lhsDiagram, {
      region: lhsDiagram.root, regions: [], nodes: [], wires: [],
    }),
  })
  const rhsBuilder = new DiagramBuilder()
  const outer = rhsBuilder.cut(rhsBuilder.root)
  rhsBuilder.cut(outer)
  const rhs = mkDiagramWithBoundary(rhsBuilder.build(), [])
  const base = verifyTheory(tinyTheory())
  const ctx = registerTheorem(base, {
    name: 'AllForwardCanonical',
    lhs,
    rhs,
    actions: [action],
  })
  const theorem = ctx.theorems.get('AllForwardCanonical')!
  return {
    ctx,
    theorem,
    computed: applyAction(theorem.lhs.diagram, theorem.actions[0]!, ctx, 'forward'),
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
    expect(sameDiagram(
      replay.diagramAt(0), theorem.lhs.diagram,
      replay.boundaryAt(0), theorem.lhs.boundary,
    )).toBe(true)
    expect(sameDiagram(
      replay.diagramAt(replay.meetingIndex), meet,
      replay.boundaryAt(replay.meetingIndex), [],
    )).toBe(true)
    expect(replay.diagramAt(replay.actionCount)).toBe(theorem.rhs.diagram)
    expect(sameDiagram(
      replay.diagramAt(replay.actionCount), theorem.rhs.diagram,
      replay.boundaryAt(replay.actionCount), theorem.rhs.boundary,
    )).toBe(true)

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

  it('uses the exact declared RHS as the shared meet/RHS representative for an all-forward proof', () => {
    const { ctx, theorem, computed } = allForwardCanonicalFixture()
    const replay = mkReplay(theorem.name, ctx)

    expect(computed).not.toBe(theorem.rhs.diagram)
    expect(sameDiagram(
      computed, theorem.rhs.diagram,
      theorem.lhs.boundary, theorem.rhs.boundary,
    )).toBe(true)
    expect(replay.meetingIndex).toBe(replay.actionCount)
    expect(replay.actionCount).toBe(1)
    expect(replay.transitions).toHaveLength(1)
    expect(replay.transitions[0]).toMatchObject({
      half: 'forward',
      action: theorem.actions[0],
      appliedFrom: theorem.lhs.diagram,
      orientation: 'forward',
    })
    expect(replay.diagramAt(replay.actionCount)).toBe(theorem.rhs.diagram)
    expect(replay.boundaryAt(replay.actionCount)).toBe(theorem.rhs.boundary)
  })

  it('ends zeroIsNat at its declared RHS with the folded nat reference visible', () => {
    const ctx = verifyTheory(buildFregeTheory())
    const theorem = ctx.theorems.get('zeroIsNat')!
    const replay = mkReplay('zeroIsNat', ctx)
    const final = replay.diagramAt(replay.actionCount)

    expect(final).toBe(theorem.rhs.diagram)
    expect(sameDiagram(
      final, theorem.rhs.diagram,
      replay.boundaryAt(replay.actionCount), theorem.rhs.boundary,
    )).toBe(true)
    expect(Object.values(final.nodes).some((node) =>
      node.kind === 'ref' && node.defId === 'nat')).toBe(true)
  })
})
