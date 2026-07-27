import { describe, expect, it } from 'vitest'
import { seedReplayPlacements } from '../../src/app/proof-placement'
import type { Replay } from '../../src/app/replay'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { applyAction, introducedNodeIds, singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import { UNARY, tinyTheory } from '../fixtures/zero-signature'

describe('replay placement reconstruction', () => {
  it('replays the original backward prefix from rhs with backward orientation', () => {
    const rhs = new DiagramBuilder().build()
    const backward = singleStepAction(
      'spawn from rhs',
      {
        rule: 'refSpawn',
        region: rhs.root,
        defId: 'UnaryWitness',
        sig: UNARY,
      },
      [{ introducedNode: 0, x: 34, y: 55 }],
    )
    const ctx = verifyTheory(tinyTheory())
    const afterBackward = applyAction(rhs, backward, ctx, 'backward')
    const introduced = introducedNodeIds(rhs, afterBackward)[0]!
    const body = { pos: { x: 0, y: 0 } }
    const replay = {
      actionCount: 2,
      meetingIndex: 0,
      transitions: [
        {
          half: 'backward',
          action: singleStepAction('later backward action', {
            rule: 'doubleCutIntro',
            sel: { region: rhs.root, regions: [], nodes: [], wires: [] },
          }),
          appliedFrom: afterBackward,
          orientation: 'backward',
        },
        {
          half: 'backward',
          action: backward,
          appliedFrom: rhs,
          orientation: 'backward',
        },
      ],
      diagramAt: (cursor: number) => cursor === 2 ? rhs : afterBackward,
    } as unknown as Replay

    seedReplayPlacements(
      { bodies: new Map([[introduced, body]]) } as never,
      replay,
      1,
      ctx,
    )

    expect(body.pos).toEqual({ x: 34, y: 55 })
  })
})
