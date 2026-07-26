import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import {
  applyTrack,
  currentTrack,
  declareTrack,
  redoTrack,
  startSession,
  startTrack,
  undoTrack,
} from '../../src/app/session'
import { tinyTheory } from '../fixtures/zero-signature'

function emptyOrigin() {
  const diagram = new DiagramBuilder().build()
  return mkDiagramWithBoundary(diagram, [])
}

describe('proof sessions over structural graphs', () => {
  it('records, undoes, and redoes a structural action', () => {
    const origin = emptyOrigin()
    const ctx = verifyTheory(tinyTheory())
    const selection = mkSelection(origin.diagram, {
      region: origin.diagram.root, regions: [], nodes: [], wires: [],
    })
    const action = singleStepAction('Wrap empty area', {
      rule: 'doubleCutIntro',
      sel: selection,
    })
    const advanced = applyTrack(startTrack(origin, 'forward', ctx), action)
    expect(advanced.timeline.cursor).toBe(1)
    expect(Object.keys(currentTrack(advanced).regions)).toHaveLength(3)
    expect(redoTrack(undoTrack(advanced)).timeline.cursor).toBe(1)
    expect(declareTrack(advanced, 'DoubleNegation').actions).toHaveLength(1)
  })

  it('starts a met fixed-side session for identical boundaries', () => {
    const origin = emptyOrigin()
    const session = startSession(origin, origin, verifyTheory(tinyTheory()))
    expect(session.forward.cursor).toBe(0)
    expect(session.backward.cursor).toBe(0)
  })
})
