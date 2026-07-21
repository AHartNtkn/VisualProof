import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import {
  artifactTheoremContext,
  artifactTheoremName,
  certifyCompletedArtifact,
  completedArtifactTheorem,
} from '../../src/game/artifact-theorem'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { applyGameAction, currentDiagram, startPuzzle } from '../../src/game/session'
import { singleStepAction } from '../../src/kernel/proof/action'
import { buildTestCatalog, minimalSource } from './catalog-fixture'
import { twoVeils } from './fixtures'

const source = minimalSource()
const catalog = buildTestCatalog(source)
const puzzle = catalog.puzzle(catalog.puzzleIds[0]!)
const fixture = twoVeils()
const completionAction = singleStepAction('remove veil pair', {
  rule: 'doubleCutElim',
  region: fixture.eliminations[0]!,
})
const noArtifacts = new Map()
const completed = certifyCompletedArtifact(catalog, noArtifacts, puzzle, [completionAction])
const unavailable = artifactTheoremContext(catalog, noArtifacts)
const available = artifactTheoremContext(catalog, new Map([[puzzle.id, completed]]))

describe('completed artifact theorems', () => {
  it('constructs the verified runtime endpoint theorem from the retained player proof', () => {
    const theorem = completedArtifactTheorem(puzzle, [completionAction])
    expect(theorem.name).toBe(`game:artifact:${puzzle.id}`)
    expect(exploreForm(theorem.lhs.diagram)).toBe(exploreForm(blankDiagram()))
    expect(theorem.rhs.diagram).toBe(puzzle.diagram)
    expect(theorem.actions).toEqual([])
    expect(theorem.backActions).toEqual([completionAction])
  })

  it('is absent before completion and present after completion', () => {
    expect(unavailable.theorems.has(artifactTheoremName(puzzle.id))).toBe(false)
    expect(exploreForm(available.theorems.get(artifactTheoremName(puzzle.id))!.rhs.diagram))
      .toBe(exploreForm(puzzle.diagram))
  })

  it('rejects retained witnesses that continue within or after the first completion', () => {
    const finishThenContinue = {
      label: 'finish then continue',
      steps: [
        completionAction.steps[0]!,
        { rule: 'doubleCutIntro' as const, sel: { region: puzzle.diagram.root, regions: [], nodes: [], wires: [] } },
        { rule: 'doubleCutElim' as const, region: 'dc' },
      ],
      placements: [],
    }
    expect(() => certifyCompletedArtifact(catalog, noArtifacts, puzzle, [finishThenContinue]))
      .toThrow(/cannot continue after reaching canonical blank/)
    expect(() => certifyCompletedArtifact(catalog, noArtifacts, puzzle, [
      completionAction,
      singleStepAction('post-completion edit', {
        rule: 'doubleCutIntro',
        sel: { region: puzzle.diagram.root, regions: [], nodes: [], wires: [] },
      }),
    ])).toThrow(/continues after action 0 reached canonical blank/)
  })

  it('manifests in a legal negative host during backward play', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const hostPuzzle = { id: puzzle.id, diagram: host.build() }
    const step = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'forward' as const,
      at: { sel: { region: negative, regions: [], nodes: [], wires: [] }, args: [] },
    }
    const action = singleStepAction('manifest artifact', step)
    const transition = applyGameAction(startPuzzle(hostPuzzle), action, { context: available })
    expect(transition.session.timeline.actions).toEqual([action])
  })

  it('dissolves an exact occurrence in a legal positive host', () => {
    const step = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'reverse' as const,
      at: {
        sel: { region: puzzle.diagram.root, regions: [fixture.eliminations[0]!], nodes: [], wires: [] },
        args: [],
      },
    }
    const transition = applyGameAction(startPuzzle(puzzle), singleStepAction('dissolve artifact', step), { context: available })
    expect(transition.completedNow).toBe(true)
    expect(isBlank(currentDiagram(transition.session))).toBe(true)
  })

  it('refuses unavailable or inexact occurrences atomically', () => {
    const session = startPuzzle(puzzle)
    const missing = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'reverse' as const,
      at: { sel: { region: puzzle.diagram.root, regions: [], nodes: [], wires: [] }, args: [] },
    }
    expect(() => applyGameAction(session, singleStepAction('missing', missing), { context: unavailable })).toThrow(/unknown theorem/)
    expect(() => applyGameAction(session, singleStepAction('inexact', missing), { context: available })).toThrow(/not an occurrence/)
    expect(currentDiagram(session)).toBe(puzzle.diagram)
  })
})
