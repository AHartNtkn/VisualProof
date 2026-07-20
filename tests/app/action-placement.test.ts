import { describe, expect, it } from 'vitest'
import { mkDiagram } from '../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { applyAction, type ProofAction } from '../../src/kernel/proof/action'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { theoremFromJson, theoremToJson } from '../../src/kernel/proof/json'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkReplay } from '../../src/app/replay'
import { mkEngine } from '../../src/view/engine'
import { seedActionHistoryPlacements } from '../../src/app/proof-placement'
import { seedProject } from '../../src/view/relax'

const context = EMPTY_PROOF_CONTEXT

describe('proof action placement presentation', () => {
  it('restores every surviving placement in the active action-history prefix', () => {
    const term = parseTerm('\\x. x')
    const start = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
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
    const first = applyAction(start, actions[0]!, context)
    const second = applyAction(first, actions[1]!, context)
    const engine = mkEngine(second, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, start, actions, context, 'forward')

    expect(engine.bodies.get('r0_intro')!.pos).toEqual({ x: -120, y: 80 })
    expect(engine.bodies.get('r0_intro_0')!.pos).toEqual({ x: 190, y: -70 })
  })

  it('does not apply a deleted body placement to a later body that reuses its id', () => {
    const term = parseTerm('\\x. x')
    const start = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const actions: ProofAction[] = [
      {
        label: 'introduce old r0_intro',
        steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
        placements: [{ introducedNode: 0, x: 999, y: 999 }],
      },
      { label: 'remove old r0_intro', steps: [{ rule: 'erasure', sel: { region: 'r0', regions: [], nodes: ['r0_intro'], wires: ['r0_intro'] } }], placements: [] },
      { label: 'introduce new r0_intro', steps: [{ rule: 'closedTermIntro', region: 'r0', term }], placements: [] },
    ]
    const final = actions.reduce((diagram, action) => applyAction(diagram, action, context), start)
    const engine = mkEngine(final, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, start, actions, context, 'forward')

    expect(engine.bodies.get('r0_intro')!.pos).not.toEqual({ x: 999, y: 999 })
  })

  it('ends a placement epoch when one multi-step action erases and recreates the same id', () => {
    const term = parseTerm('\\x. x')
    const start = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const introduce: ProofAction = {
      label: 'place original r0_intro',
      steps: [{ rule: 'closedTermIntro', region: 'r0', term }],
      placements: [{ introducedNode: 0, x: 999, y: 999 }],
    }
    const original = applyAction(start, introduce, context)
    expect(Object.keys(original.nodes)).toEqual(['r0_intro'])
    const replaceInOneAction: ProofAction = {
      label: 'replace r0_intro within one action',
      steps: [
        { rule: 'erasure', sel: { region: 'r0', regions: [], nodes: ['r0_intro'], wires: ['r0_intro'] } },
        { rule: 'closedTermIntro', region: 'r0', term },
      ],
      placements: [],
    }
    const replacement = applyAction(original, replaceInOneAction, context)
    expect(Object.keys(replacement.nodes)).toEqual(['r0_intro'])
    const engine = mkEngine(replacement, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, start, [introduce, replaceInOneAction], context, 'forward')

    expect(engine.bodies.get('r0_intro')!.pos).not.toEqual({ x: 999, y: 999 })
  })

  it('maps placements to lexically ordered introduced-node indices only after the complete action', () => {
    const before = mkDiagram({ root: 'r0', regions: { r0: { kind: 'sheet' } } })
    const term = parseTerm('\\x. x')
    const action: ProofAction = {
      label: 'twelve placed terms',
      steps: Array.from({ length: 12 }, () => ({ rule: 'closedTermIntro' as const, region: 'r0', term })),
      placements: [
        { introducedNode: 0, x: 101, y: 202 },
        { introducedNode: 3, x: 303, y: 404 },
      ],
    }
    const after = applyAction(before, action, context)
    const engine = mkEngine(after, [])
    seedProject(engine)

    seedActionHistoryPlacements(engine, before, [action], context, 'forward')

    expect(engine.bodies.get('r0_intro')!.pos).toEqual({ x: 101, y: 202 })
    expect(engine.bodies.get('r0_intro_10')!.pos).toEqual({ x: 303, y: 404 })
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
    const engine = mkEngine(replayed, replay.boundaryAt(1))
    seedProject(engine)

    seedActionHistoryPlacements(
      engine,
      replay.diagramAt(0),
      replay.actions,
      context,
      'forward',
    )

    const introduced = Object.keys(replayed.nodes).find((id) => before.nodes[id] === undefined)!
    expect(engine.bodies.get(introduced)!.pos).toEqual({ x: -77, y: 143 })
  })
})
