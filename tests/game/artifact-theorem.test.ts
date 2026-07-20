import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { artifactTheoremContext, artifactTheoremName, completedArtifactTheorem } from '../../src/game/artifact-theorem'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { applyGameStep, currentDiagram, startPuzzle } from '../../src/game/session'
import { buildTestCatalog, minimalSource } from './catalog-fixture'
import { twoVeils } from './fixtures'

const source = minimalSource()
const catalog = buildTestCatalog(source)
const puzzle = catalog.puzzle(catalog.puzzleIds[0]!)
const fixture = twoVeils()
const unavailable = artifactTheoremContext(catalog, new Set())
const available = artifactTheoremContext(catalog, new Set([puzzle.id]))

describe('completed artifact theorems', () => {
  it('constructs the verified runtime endpoint theorem without a shipped proof recording', () => {
    const theorem = completedArtifactTheorem(puzzle)
    expect(theorem.name).toBe(`game:artifact:${puzzle.id}`)
    expect(exploreForm(theorem.lhs.diagram)).toBe(exploreForm(blankDiagram()))
    expect(theorem.rhs.diagram).toBe(puzzle.diagram)
    expect(theorem.steps).toEqual([])
    expect(theorem.backSteps).toEqual([])
  })

  it('is absent before completion and present after completion', () => {
    expect(unavailable.theorems.has(artifactTheoremName(puzzle.id))).toBe(false)
    expect(available.theorems.get(artifactTheoremName(puzzle.id))?.rhs.diagram).toBe(puzzle.diagram)
  })

  it('manifests in a legal negative host during backward play', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const hostPuzzle = { id: puzzle.id, diagram: host.build() }
    const step = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'forward' as const,
      at: { sel: { region: negative, regions: [], nodes: [], wires: [] }, args: [] },
    }
    const transition = applyGameStep(startPuzzle(hostPuzzle), step, { context: available })
    expect(transition.session.timeline.steps).toEqual([step])
  })

  it('dissolves an exact occurrence in a legal positive host', () => {
    const step = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'reverse' as const,
      at: {
        sel: { region: puzzle.diagram.root, regions: [fixture.eliminations[0]!], nodes: [], wires: [] },
        args: [],
      },
    }
    const transition = applyGameStep(startPuzzle(puzzle), step, { context: available })
    expect(transition.completedNow).toBe(true)
    expect(isBlank(currentDiagram(transition.session))).toBe(true)
  })

  it('refuses unavailable or inexact occurrences atomically', () => {
    const session = startPuzzle(puzzle)
    const missing = {
      rule: 'theorem' as const, name: artifactTheoremName(puzzle.id), direction: 'reverse' as const,
      at: { sel: { region: puzzle.diagram.root, regions: [], nodes: [], wires: [] }, args: [] },
    }
    expect(() => applyGameStep(session, missing, { context: unavailable })).toThrow(/unknown theorem/)
    expect(() => applyGameStep(session, missing, { context: available })).toThrow(/not an occurrence/)
    expect(currentDiagram(session)).toBe(puzzle.diagram)
  })
})
