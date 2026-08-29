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
import { proofTermSpawnStep } from '../../src/app/interact/proof-spawn'
import { convertToNormal } from '../../src/app/tactics'
import { parseTerm } from '../../src/kernel/term/parse'
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

  it('undoes and redoes Lambda spawning and normalization as exact proof actions', () => {
    const builder = new DiagramBuilder()
    const region = builder.cut(builder.root)
    const origin = mkDiagramWithBoundary(builder.build(), [])
    const ctx = verifyTheory(tinyTheory())
    let track = applyTrack(startTrack(origin, 'forward', ctx), singleStepAction(
      'Lambda expression',
      proofTermSpawnStep(parseTerm('(\\x. x) a'), region),
      [{ introducedNode: 0, x: 60, y: 90 }],
    ))
    const spawned = currentTrack(track)
    const entry = Object.entries(spawned.nodes).find(([, node]) => node.kind === 'term')
    if (entry === undefined) throw new Error('Lambda session fixture has no term node')
    track = applyTrack(track, singleStepAction(
      'Normalize Lambda term',
      convertToNormal(spawned, entry[0], 64).step,
    ))

    const normalized = currentTrack(track)
    const undone = undoTrack(track)
    const redone = redoTrack(undone)
    expect(track.timeline.actions.map((action) => action.steps.map((step) => step.rule)))
      .toEqual([['lambdaTermSpawn'], ['lambdaConversion']])
    expect(currentTrack(undone)).toBe(spawned)
    expect(currentTrack(redone)).toBe(normalized)
    expect(declareTrack(redone, 'LambdaHistory').actions).toHaveLength(2)
  })
})
