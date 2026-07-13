import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { parseTerm } from '../../src/kernel/term/parse'
import type { ProofAction } from '../../src/kernel/proof/action'
import type { ProofTimeline } from '../../src/app/session'
import { proofSnapshot } from '../../src/app/proof-snapshot'

function timeline(diagram: ReturnType<typeof mkDiagram>, actions: readonly ProofAction[] = []): ProofTimeline {
  return {
    states: actions.length === 0 ? [diagram] : [diagram, diagram],
    actions,
    cursor: actions.length,
  }
}

describe('authoritative proof snapshots', () => {
  it('distinguishes equal endpoint counts wired to different ports', () => {
    const node = { kind: 'term' as const, region: 'r0', term: parseTerm('x') }
    const output = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: node },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x' } }] },
      },
    })
    const freeVariable = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      nodes: { n0: node },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'freeVar', name: 'x' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
      },
    })

    expect(JSON.stringify(proofSnapshot(timeline(output), 'forward')))
      .not.toBe(JSON.stringify(proofSnapshot(timeline(freeVariable), 'forward')))
  })

  it('distinguishes same-label actions with different step content', () => {
    const diagram = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const action = (arity: number): ProofAction => ({
      label: 'same label',
      steps: [{ rule: 'vacuousIntro', sel: { region: 'r0', regions: [], nodes: [], wires: [] }, arity }],
      placements: [],
    })

    expect(JSON.stringify(proofSnapshot(timeline(diagram, [action(0)]), 'forward')))
      .not.toBe(JSON.stringify(proofSnapshot(timeline(diagram, [action(1)]), 'forward')))
  })
})
