import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import { mkReplay } from '../../src/app/replay'
import { applyTrack, declareTrack, startTrack } from '../../src/app/session'
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

describe('structural replay', () => {
  it('exposes action labels, steps, diagrams, and transported boundaries', () => {
    const { ctx } = replayFixture()
    const replay = mkReplay('DoubleNegation', ctx)
    expect(replay.actionCount).toBe(1)
    expect(replay.labelAt(1)).toBe('Double cut')
    expect(replay.stepsAt(1)[0]?.rule).toBe('doubleCutIntro')
    expect(Object.keys(replay.diagramAt(1).regions)).toHaveLength(3)
    expect(replay.boundaryAt(1)).toEqual([])
    expect(() => replay.diagramAt(2)).toThrow(/out of range/)
  })
})
