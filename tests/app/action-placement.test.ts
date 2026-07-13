import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { theoremFromJson, theoremToJson } from '../../src/kernel/proof/json'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkReplay } from '../../src/app/replay'
import { mkEngine } from '../../src/view/engine'
import { seedActionPlacements } from '../../src/view/placement'
import { seedProject } from '../../src/view/relax'

const context = { theorems: new Map(), relations: new Map() }

describe('proof action placement presentation', () => {
  it('maps placements to lexically ordered introduced-node indices only after the complete action', () => {
    const before = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const term = parseTerm('\\x. x')
    const after = mkDiagram({
      root: 'r0', regions: { r0: { kind: 'sheet' } },
      nodes: {
        n2: { kind: 'term', region: 'r0', term },
        n10: { kind: 'term', region: 'r0', term },
      },
      wires: {
        w2: { scope: 'r0', endpoints: [{ node: 'n2', port: { kind: 'output' } }] },
        w10: { scope: 'r0', endpoints: [{ node: 'n10', port: { kind: 'output' } }] },
      },
    })
    const engine = mkEngine(after, [])
    seedProject(engine)

    seedActionPlacements(engine, before, after, [
      { introducedNode: 0, x: 101, y: 202 },
      { introducedNode: 1, x: 303, y: 404 },
    ])

    expect(engine.bodies.get('n10')!.pos).toEqual({ x: 101, y: 202 })
    expect(engine.bodies.get('n2')!.pos).toEqual({ x: 303, y: 404 })
  })

  it('presents placement from a persisted theorem action at replay state k', () => {
    const before = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const action: ProofAction = {
      label: 'placed closed term',
      steps: [{ rule: 'closedTermIntro', region: 'r0', term: parseTerm('\\x. x') }],
      placements: [{ introducedNode: 0, x: -77, y: 143 }],
    }
    const after = applyAction(before, action, context)
    const theorem = theoremFromJson(theoremToJson({
      name: 'placed-replay',
      lhs: mkDiagramWithBoundary(before, []),
      rhs: mkDiagramWithBoundary(after, []),
      actions: [action],
    }))
    const replay = mkReplay(theorem, context)
    const replayed = replay.diagramAt(1)
    const engine = mkEngine(replayed, replay.boundary)
    seedProject(engine)

    seedActionPlacements(engine, replay.diagramAt(0), replayed, replay.actions[0]!.placements)

    const introduced = Object.keys(replayed.nodes).find((id) => before.nodes[id] === undefined)!
    expect(engine.bodies.get(introduced)!.pos).toEqual({ x: -77, y: 143 })
  })
})
