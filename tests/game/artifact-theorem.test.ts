import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { checkTheorem } from '../../src/kernel/proof/theorem'
import {
  artifactTheorem,
  artifactTheoremContext,
  artifactTheoremName,
} from '../../src/game/artifact-theorem'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { applyGameStep, currentDiagram, startPuzzle } from '../../src/game/session'
import { minimalPuzzle } from './catalog-fixture'
import { fourVeils, twoVeils } from './fixtures'

const fixture = twoVeils()
const puzzle = minimalPuzzle({ name: { professional: 'Two Veils' } })
const relations = new Map()
const unavailable = artifactTheoremContext([puzzle], new Set(), { relations })
const available = artifactTheoremContext([puzzle], new Set([puzzle.id]), { relations })

describe('completed artifact theorems', () => {
  it('constructs a verified closed theorem from blank to the goal using the backward witness', () => {
    const theorem = artifactTheorem(puzzle, unavailable)

    expect(theorem.name).toBe(`game:artifact:${puzzle.id}`)
    expect(exploreForm(theorem.lhs.diagram)).toBe(exploreForm(blankDiagram()))
    expect(theorem.lhs.boundary).toEqual([])
    expect(theorem.rhs).toEqual(puzzle.goal)
    expect(theorem.steps).toEqual([])
    expect(theorem.backSteps).toEqual(puzzle.witness)
    expect(() => checkTheorem(theorem, unavailable)).not.toThrow()
  })

  it('is absent before completion and present after completion', () => {
    expect(unavailable.theorems.has(artifactTheoremName(puzzle.id))).toBe(false)
    expect(available.theorems.get(artifactTheoremName(puzzle.id))).toMatchObject({
      name: artifactTheoremName(puzzle.id),
      rhs: puzzle.goal,
    })
  })

  it('manifests forward in a legal negative host during backward play', () => {
    const host = new DiagramBuilder()
    const negative = host.cut(host.root)
    const hostPuzzle = minimalPuzzle({
      id: puzzle.id,
      goal: mkDiagramWithBoundary(host.build(), []),
    })
    const step = {
      rule: 'theorem' as const,
      name: artifactTheoremName(puzzle.id),
      direction: 'forward' as const,
      at: { sel: { region: negative, regions: [], nodes: [], wires: [] }, args: [] },
    }

    const transition = applyGameStep(startPuzzle(hostPuzzle), step, { context: available })

    expect(transition.session.timeline.steps).toEqual([step])
    expect(transition.session.timeline.steps[0]?.rule).toBe('theorem')
    expect(Object.values(currentDiagram(transition.session).regions)
      .filter((region) => region.kind === 'cut')).toHaveLength(3)
  })

  it('dissolves an exact rhs occurrence in a legal positive host during backward play', () => {
    const step = {
      rule: 'theorem' as const,
      name: artifactTheoremName(puzzle.id),
      direction: 'reverse' as const,
      at: {
        sel: {
          region: puzzle.goal.diagram.root,
          regions: [fixture.eliminations[0]!],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    }

    const transition = applyGameStep(startPuzzle(puzzle), step, { context: available })

    expect(transition.session.timeline.steps).toEqual([step])
    expect(transition.completedNow).toBe(true)
    expect(isBlank(currentDiagram(transition.session))).toBe(true)
  })

  it('refuses a strict subgraph atomically', () => {
    const strictSubgraph = {
      rule: 'theorem' as const,
      name: artifactTheoremName(puzzle.id),
      direction: 'reverse' as const,
      at: {
        sel: {
          region: puzzle.goal.diagram.root,
          regions: [],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    }
    const session = startPuzzle(puzzle)
    const before = exploreForm(currentDiagram(session))

    expect(() => applyGameStep(session, strictSubgraph, { context: available }))
      .toThrow(/not an occurrence/)
    expect(exploreForm(currentDiagram(session))).toBe(before)
    expect(session.timeline.steps).toEqual([])
    expect(session.timeline.states).toHaveLength(1)
  })

  it('refuses a wrong occurrence atomically', () => {
    const other = fourVeils()
    const otherPuzzle = minimalPuzzle({ goal: other.goal })
    const wrongOccurrence = {
      rule: 'theorem' as const,
      name: artifactTheoremName(puzzle.id),
      direction: 'reverse' as const,
      at: {
        sel: {
          region: other.goal.diagram.root,
          regions: [other.eliminations[1]!],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    }
    const session = startPuzzle(otherPuzzle)
    const before = exploreForm(currentDiagram(session))

    expect(() => applyGameStep(session, wrongOccurrence, { context: available }))
      .toThrow(/not an occurrence/)
    expect(exploreForm(currentDiagram(session))).toBe(before)
    expect(session.timeline.steps).toEqual([])
  })

  it('refuses an unavailable theorem atomically', () => {
    const step = {
      rule: 'theorem' as const,
      name: artifactTheoremName(puzzle.id),
      direction: 'reverse' as const,
      at: {
        sel: {
          region: puzzle.goal.diagram.root,
          regions: [fixture.eliminations[0]!],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    }
    const session = startPuzzle(puzzle)
    const before = exploreForm(currentDiagram(session))

    expect(() => applyGameStep(session, step, { context: unavailable }))
      .toThrow(/unknown theorem/)
    expect(exploreForm(currentDiagram(session))).toBe(before)
    expect(session.timeline.steps).toEqual([])
  })
})
