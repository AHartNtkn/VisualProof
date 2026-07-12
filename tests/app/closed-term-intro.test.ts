import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { applyStep } from '../../src/kernel/proof/step'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import {
  closedTermIntroStep,
  commitClosedTermSpawn,
  introducedNodeId,
} from '../../src/app/interact/closed-term-intro'

describe('closed-term proof spawning', () => {
  it('constructs the replayable proof step from a closed source term', () => {
    expect(closedTermIntroStep('\\x. x', 'r7')).toEqual({
      rule: 'closedTermIntro',
      region: 'r7',
      term: parseTerm('\\x. x'),
    })
  })

  it('refuses an open source term before proof commit', () => {
    expect(() => closedTermIntroStep('x', 'r7'))
      .toThrow("closed-term introduction requires a closed term; free ports ['x'] remain")
  })

  it('identifies the one node minted by the committed proof step for placement', () => {
    const before = new DiagramBuilder().build()
    const after = applyStep(
      before,
      closedTermIntroStep('\\x. x', before.root),
      { theorems: new Map(), relations: new Map() },
    )

    expect(after.nodes[introducedNodeId(before, after)]).toMatchObject({
      kind: 'term',
      region: before.root,
      term: parseTerm('\\x. x'),
    })
  })

  it('commits through the host proof path and returns the minted-node placement', () => {
    const before = new DiagramBuilder().build()
    const steps: unknown[] = []
    const invocation = {
      screen: { x: 10, y: 20 },
      world: { x: -12, y: 35 },
      region: before.root,
    }

    const result = commitClosedTermSpawn('\\x. x', invocation, before, (step) => {
      steps.push(step)
      return applyStep(before, step, { theorems: new Map(), relations: new Map() })
    })

    expect(steps).toEqual([{ rule: 'closedTermIntro', region: before.root, term: parseTerm('\\x. x') }])
    expect(result.at).toEqual(invocation.world)
    expect(result.diagram.nodes[result.node]).toMatchObject({ kind: 'term', region: before.root })
  })
})
