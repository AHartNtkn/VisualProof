import { describe, expect, it } from 'vitest'
import { seedActionHistoryPlacements } from '../../src/app/proof-placement'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import { UNARY, tinyTheory } from '../fixtures/zero-signature'

describe('proof action placement reconstruction', () => {
  it('places a node introduced by structural ref spawn', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const initial = builder.build()
    const action = singleStepAction(
      'Spawn UnaryWitness',
      {
        rule: 'refSpawn',
        region: negative,
        defId: 'UnaryWitness',
        sig: UNARY,
      },
      [{ introducedNode: 0, x: 13, y: 21 }],
    )
    const body = { pos: { x: 0, y: 0 } }
    const engine = { bodies: new Map([['n', body]]) }
    seedActionHistoryPlacements(
      engine as never,
      initial,
      [action],
      verifyTheory(tinyTheory()),
      'forward',
    )
    expect(body.pos).toEqual({ x: 13, y: 21 })
  })
})
