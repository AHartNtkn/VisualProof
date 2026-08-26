import { describe, expect, it } from 'vitest'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { registerTheorem, verifyTheory } from '../../src/kernel/proof/context'
import {
  diagramForShellSession,
  editShellSession,
  enterShellReplay,
  leaveShellReplay,
  moveShellReplay,
  proofForShellSession,
  proofShellSession,
  shellSessionBoundary,
} from '../../src/app/shell-session'
import { mkReplay } from '../../src/app/replay'
import { applyTrack, declareTrack, startTrack } from '../../src/app/session'
import { tinyTheory } from '../fixtures/zero-signature'

describe('shell session state', () => {
  it('derives replay presentation and restores the exact proof session on exit', () => {
    const diagram = new DiagramBuilder().build()
    const origin = mkDiagramWithBoundary(diagram, [])
    const context = verifyTheory(tinyTheory())
    const track = applyTrack(startTrack(origin, 'forward', context), singleStepAction(
      'Double cut',
      {
        rule: 'doubleCutIntro',
        sel: mkSelection(diagram, {
          region: diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        }),
      },
    ))
    const theorem = declareTrack(track, 'DoubleNegation')
    const replay = mkReplay(theorem.name, registerTheorem(context, theorem))
    const proofState = proofShellSession({ kind: 'track', track })

    const replayState = enterShellReplay(proofState, replay)
    const finalState = moveShellReplay(replayState, Number.POSITIVE_INFINITY)

    expect(finalState.cursor).toBe(replay.actionCount)
    expect(diagramForShellSession(finalState, diagram)).toBe(replay.diagramAt(replay.actionCount))
    expect(shellSessionBoundary(finalState)).toEqual(replay.boundaryAt(replay.actionCount))
    expect(proofForShellSession(finalState)).toBe(proofState.proof)
    expect(leaveShellReplay(finalState)).toBe(proofState)
  })

  it('derives an edit diagram without retaining a displayed-diagram mirror', () => {
    const diagram = new DiagramBuilder().build()
    const state = editShellSession()

    expect(diagramForShellSession(state, diagram)).toBe(diagram)
    expect(shellSessionBoundary(state)).toEqual([])
    expect(proofForShellSession(state)).toBeNull()
  })
})
