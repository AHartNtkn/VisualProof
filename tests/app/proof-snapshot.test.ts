import { describe, expect, it } from 'vitest'
import { proofSnapshot } from '../../src/app/proof-snapshot'
import { proofTermSpawnStep } from '../../src/app/interact/proof-spawn'
import { convertToNormal } from '../../src/app/tactics'
import { applyTrack, currentTrack, startTrack } from '../../src/app/session'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { diagramFromJson } from '../../src/kernel/diagram/json'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { singleStepAction } from '../../src/kernel/proof/action'
import { verifyTheory } from '../../src/kernel/proof/context'
import { parseTerm } from '../../src/kernel/term/parse'
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

  it('snapshots nameless Lambda spawn and conversion actions with the current structural diagram', () => {
    const builder = new DiagramBuilder()
    const region = builder.cut(builder.root)
    const origin = mkDiagramWithBoundary(builder.build(), [])
    const context = verifyTheory(tinyTheory())
    let track = applyTrack(startTrack(origin, 'forward', context), singleStepAction(
      'Lambda expression',
      proofTermSpawnStep(parseTerm('(\\x. x) a'), region),
      [{ introducedNode: 0, x: 30, y: 45 }],
    ))
    const spawned = currentTrack(track)
    const entry = Object.entries(spawned.nodes).find(([, node]) => node.kind === 'term')
    if (entry === undefined) throw new Error('Lambda snapshot fixture has no term node')
    track = applyTrack(track, singleStepAction(
      'Normalize Lambda term',
      convertToNormal(spawned, entry[0], 64).step,
    ))

    const snapshot = proofSnapshot(track.timeline, 'forward')
    expect(snapshot).toMatchObject({
      cursor: 2,
      orientation: 'forward',
      actions: [
        {
          label: 'Lambda expression',
          steps: [{ rule: 'lambdaTermSpawn', freeArity: 1 }],
          placements: [{ introducedNode: 0, x: 30, y: 45 }],
        },
        {
          label: 'Normalize Lambda term',
          steps: [{ rule: 'lambdaConversion', node: entry[0] }],
        },
      ],
    })
    const diagram = diagramFromJson(snapshot.diagram)
    const term = Object.values(diagram.nodes).find((node) => node.kind === 'term')
    expect(term).toMatchObject({ kind: 'term', term: parseTerm('a').term, freeArity: 1 })
    expect(Object.values(diagram.nodes)
      .filter((node) => node.kind === 'identity' && node.arity === 1)).toHaveLength(2)
  })
})
