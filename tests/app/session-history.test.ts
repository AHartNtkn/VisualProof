import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import {
  applyTrack,
  moveTrack,
  startTrack,
  timelineActiveActions,
} from '../../src/app/session'
import { tinyTheory } from '../fixtures/zero-signature'

describe('proof history cursor', () => {
  it('excludes redo actions from the active proof', () => {
    const diagram = new DiagramBuilder().build()
    const origin = mkDiagramWithBoundary(diagram, [])
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [], wires: [],
    })
    const action = singleStepAction('Double cut', {
      rule: 'doubleCutIntro',
      sel: selection,
    })
    const track = applyTrack(startTrack(origin, 'forward', verifyTheory(tinyTheory())), action)
    expect(timelineActiveActions(moveTrack(track, 0).timeline)).toEqual([])
    expect(timelineActiveActions(track.timeline)).toEqual([action])
  })
})
