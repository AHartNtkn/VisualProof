import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { theoremFromJson, theoremToJson } from '../../src/kernel/proof/json'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkReplay } from '../../src/app/replay'
import { mkEngine } from '../../src/view/engine'
import { seedActionHistoryPlacements } from '../../src/view/placement'
import { seedProject } from '../../src/view/relax'

const context = { theorems: new Map(), relations: new Map() }

describe('proof action placement presentation', () => {
  it('restores every surviving placement in the active action-history prefix', () => {
    const term = parseTerm('\\x. x')
    const start = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const first = mkDiagram({
      root: 'r0', regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'term', region: 'r0', term } },
      wires: { w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })
    const second = mkDiagram({
      root: 'r0', regions: { r0: { kind: 'sheet' } },
      nodes: {
        n0: { kind: 'term', region: 'r0', term },
        n1: { kind: 'term', region: 'r0', term },
      },
      wires: {
        w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] },
        w1: { scope: 'r0', endpoints: [{ node: 'n1', port: { kind: 'output' } }] },
      },
    })
    const actions: ProofAction[] = [
      {
        label: 'first placed term',
        steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
        placements: [{ introducedNode: 0, x: -120, y: 80 }],
      },
      {
        label: 'second placed term',
        steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
        placements: [{ introducedNode: 0, x: 190, y: -70 }],
      },
    ]
    const engine = mkEngine(second, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, [start, first, second], actions, 2)

    expect(engine.bodies.get('n0')!.pos).toEqual({ x: -120, y: 80 })
    expect(engine.bodies.get('n1')!.pos).toEqual({ x: 190, y: -70 })
  })

  it('does not apply a deleted body placement to a later body that reuses its id', () => {
    const term = parseTerm('\\x. x')
    const empty = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const withNode = mkDiagram({
      root: 'r0', regions: { r0: { kind: 'sheet' } },
      nodes: { n0: { kind: 'term', region: 'r0', term } },
      wires: { w0: { scope: 'r0', endpoints: [{ node: 'n0', port: { kind: 'output' } }] } },
    })
    const actions: ProofAction[] = [
      {
        label: 'introduce old n0',
        steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
        placements: [{ introducedNode: 0, x: 999, y: 999 }],
      },
      { label: 'remove old n0', steps: [{ rule: 'erasure', sel: { region: 'r0', regions: [], nodes: ['n0'], wires: ['w0'] } }], placements: [] },
      { label: 'introduce new n0', steps: [{ rule: 'closedTermIntro', region: 'r0', term }], placements: [] },
    ]
    const engine = mkEngine(withNode, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, [empty, withNode, empty, withNode], actions, 3)

    expect(engine.bodies.get('n0')!.pos).not.toEqual({ x: 999, y: 999 })
  })

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

    seedActionHistoryPlacements(engine, [before, after], [{
      label: 'two placed terms',
      steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
      placements: [
        { introducedNode: 0, x: 101, y: 202 },
        { introducedNode: 1, x: 303, y: 404 },
      ],
    }], 1)

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

    seedActionHistoryPlacements(
      engine,
      [replay.diagramAt(0), replayed],
      replay.actions,
      1,
    )

    const introduced = Object.keys(replayed.nodes).find((id) => before.nodes[id] === undefined)!
    expect(engine.bodies.get(introduced)!.pos).toEqual({ x: -77, y: 143 })
  })
})
