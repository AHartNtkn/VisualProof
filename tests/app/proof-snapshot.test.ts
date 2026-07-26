import { describe, expect, it } from 'vitest'
import { proofSnapshot } from '../../src/app/proof-snapshot'
import { applyTrack, startTrack } from '../../src/app/session'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import { tinyTheory } from '../fixtures/zero-signature'

describe('authoritative proof snapshots', () => {
  it('serializes the active structural proof vocabulary', () => {
    const diagram = new DiagramBuilder().build()
    const origin = mkDiagramWithBoundary(diagram, [])
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [], wires: [],
    })
    const track = applyTrack(
      startTrack(origin, 'forward', verifyTheory(tinyTheory())),
      singleStepAction('Double cut', { rule: 'doubleCutIntro', sel: selection }),
    )
    expect(proofSnapshot(track.timeline, 'forward')).toMatchObject({
      cursor: 1,
      orientation: 'forward',
      actions: [{
        label: 'Double cut',
        steps: [{ rule: 'doubleCutIntro' }],
      }],
    })
  })
})
