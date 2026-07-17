import { describe, expect, it } from 'vitest'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { buildCatalog } from '../../src/game/catalog'
import { artifactTheoremName } from '../../src/game/artifact-theorem'
import { blankDiagram, isBlank } from '../../src/game/blank'
import { createInitialGameState } from '../../src/game/controller-state'
import { reduceGame } from '../../src/game/controller'
import { decodeGameSave, encodeGameSave } from '../../src/game/save'
import { applyGameStep, currentDiagram, startPuzzle } from '../../src/game/session'
import {
  cultureId, GameDomainError, performanceId, puzzleId,
  type CultureDefinition, type PuzzleDefinition, type PuzzleId, type TeacherIntervention,
} from '../../src/game/types'
import { fixturePerformanceId, minimalPerformance, minimalPuzzle, minimalSource } from './catalog-fixture'
import { fourVeils, twoVeils } from './fixtures'

const fixture = twoVeils()
const puzzle = minimalPuzzle({ name: { professional: 'Two Veils' } })
const culture = minimalSource().cultures[0]!
const four = fourVeils()
const reachedTwoVeils = {
  id: 'inner-pair-removed',
  performance: fixturePerformanceId,
  trigger: {
    kind: 'recognizedUnwinnable',
    state: twoVeils().goal,
    demonstration: [{ rule: 'doubleCutElim', region: four.eliminations[0]! }],
  },
  text: 'That route leaves the older paired form.',
  repeat: 'once',
  recovery: 'timeline',
} satisfies TeacherIntervention
const fourPuzzle = minimalPuzzle({
  goal: four.goal,
  witness: [
    { rule: 'doubleCutElim', region: four.eliminations[0]! },
    { rule: 'doubleCutElim', region: four.eliminations[1]! },
  ],
  teacher: [reachedTwoVeils],
})

describe('verified game catalog', () => {
  it('accepts a closed puzzle whose backward witness reaches blank', () => {
    const catalog = buildCatalog({ ...minimalSource(), puzzles: [puzzle] })
    expect(catalog.puzzle(puzzle.id)).toStrictEqual(puzzle)
    expect(catalog.puzzle(puzzle.id)).not.toBe(puzzle)
  })

  it('rejects missing prerequisites and dependency cycles', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [{ ...puzzle, prerequisites: [puzzleId('missing')] }],
    })).toThrow(/missing prerequisite/)
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [{ ...puzzle, prerequisites: [puzzle.id] }],
    })).toThrow(/dependency cycle/)
  })

  it('rejects a missing culture gateway', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, gateway: puzzleId('missing') }],
    })).toThrow(/missing gateway/)
  })

  it('rejects a culture gateway owned by another culture', () => {
    const otherCulture = cultureId('other-tradition')
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [culture, {
        ...culture, id: otherCulture, name: 'Other culture', relativeAge: 1,
      }],
    })).toThrow(/gateway.*belongs to culture/)
  })

  it('rejects missing and duplicate culture unlock artifacts', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, unlocksAfter: [puzzleId('missing')] }],
    })).toThrow(/missing unlock artifact/)
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, unlocksAfter: [puzzle.id, puzzle.id] }],
    })).toThrow(/duplicate unlock artifact/)
  })

  it('rejects culture dependency self-edges and cycles', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, unlocksAfter: [puzzle.id] }],
    })).toThrow(/depends on itself/)

    const otherCultureId = cultureId('other-tradition')
    const otherPuzzle = minimalPuzzle({
      id: puzzleId('other-gateway'), culture: otherCultureId,
      name: { professional: 'Other gateway' },
    })
    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [
        { ...culture, unlocksAfter: [otherPuzzle.id] },
        {
          ...culture,
          id: otherCultureId,
          name: 'Other culture',
          relativeAge: 1,
          unlocksAfter: [puzzle.id],
          gateway: otherPuzzle.id,
        },
      ],
      puzzles: [puzzle, otherPuzzle],
    })).toThrow(/culture dependency cycle/)
  })

  it('rejects a deadlock formed jointly by culture gates and puzzle prerequisites', () => {
    const secondCultureId = cultureId('second-tradition')
    const firstGateway = minimalPuzzle({
      id: puzzleId('gateway-a'),
      prerequisites: [puzzleId('gateway-b')],
    })
    const secondGateway = minimalPuzzle({
      id: puzzleId('gateway-b'),
      culture: secondCultureId,
      name: { professional: 'Second gateway' },
    })

    expect(() => buildCatalog({
      ...minimalSource(),
      cultures: [
        { ...culture, gateway: firstGateway.id },
        {
          ...culture,
          id: secondCultureId,
          name: 'Second culture',
          relativeAge: 1,
          unlocksAfter: [firstGateway.id],
          gateway: secondGateway.id,
        },
      ],
      puzzles: [firstGateway, secondGateway],
    })).toThrow(
      "unreachable puzzles 'gateway-a', 'gateway-b' in cultures 'oldest-tradition', 'second-tradition'",
    )
  })

  it('accepts staged progression across culture gates and puzzle prerequisites', () => {
    const secondCultureId = cultureId('second-tradition')
    const firstGateway = minimalPuzzle({ id: puzzleId('gateway-a') })
    const secondGateway = minimalPuzzle({
      id: puzzleId('gateway-b'),
      culture: secondCultureId,
      name: { professional: 'Second gateway' },
      prerequisites: [firstGateway.id],
    })

    const catalog = buildCatalog({
      ...minimalSource(),
      cultures: [
        { ...culture, gateway: firstGateway.id },
        {
          ...culture,
          id: secondCultureId,
          name: 'Second culture',
          relativeAge: 1,
          unlocksAfter: [firstGateway.id],
          gateway: secondGateway.id,
        },
      ],
      puzzles: [firstGateway, secondGateway],
    })

    expect(catalog.puzzle(secondGateway.id)).toStrictEqual(secondGateway)
  })

  it('rejects a witness that does not reach blank', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [{ ...puzzle, witness: [], learning: { ...puzzle.learning, rulesUsed: [] } }],
    })).toThrow(/witness does not reach blank/)
  })

  it('rejects a witness that passes through blank and continues', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [{
        ...puzzle,
        learning: { ...puzzle.learning, rulesUsed: ['doubleCutElim', 'doubleCutIntro'] },
        witness: [
          ...puzzle.witness,
          {
            rule: 'doubleCutIntro' as const,
            sel: { region: fixture.goal.diagram.root, regions: [], nodes: [], wires: [] },
          },
          { rule: 'doubleCutElim' as const, region: 'dc0' },
        ],
      }],
    })).toThrow(GameDomainError)
  })

  it('rejects incomplete artifact nomenclature and provenance', () => {
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({ name: { professional: '  ' } })],
    })).toThrow(/professional/)
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({
        provenance: { summary: '', function: 'Supports a minimal verified witness.' },
      })],
    })).toThrow(/provenance summary/)
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({ name: {
        professional: 'Fixture artifact', curatorShorthand: ' padded ',
      } })],
    })).toThrow(/curator shorthand/)
  })

  it('rejects cultures without sealing vocabulary', () => {
    expect(() => buildCatalog({
      ...minimalSource(), cultures: [{ ...culture, sealingVocabulary: [] }],
    })).toThrow(/sealing vocabulary/)
  })

  it('requires two to five unique knowledge points per performance', () => {
    const point = minimalPerformance().knowledgePoints[0]!
    expect(() => buildCatalog({
      ...minimalSource(), performances: [minimalPerformance({ knowledgePoints: [point] })],
    })).toThrow(/two to five knowledge points/)
    expect(() => buildCatalog({
      ...minimalSource(),
      performances: [minimalPerformance({ knowledgePoints: Array.from({ length: 6 }, (_, index) => ({
        ...point, id: `point-${index}`,
      })) })],
    })).toThrow(/two to five knowledge points/)
    expect(() => buildCatalog({
      ...minimalSource(), performances: [minimalPerformance({ knowledgePoints: [point, point] })],
    })).toThrow(/duplicate knowledge point/)
  })

  it('rejects missing performance prerequisites and prerequisite cycles', () => {
    expect(() => buildCatalog({
      ...minimalSource(),
      performances: [minimalPerformance({ prerequisites: [performanceId('missing')] })],
    })).toThrow(/missing performance prerequisite/)

    const otherId = performanceId('other-performance')
    expect(() => buildCatalog({
      ...minimalSource(),
      performances: [
        minimalPerformance({ prerequisites: [otherId] }),
        minimalPerformance({ id: otherId, prerequisites: [fixturePerformanceId] }),
      ],
    })).toThrow(/performance prerequisite cycle/)
  })

  it('rejects unknown and duplicate puzzle learning-role entries', () => {
    const roles = ['introduces', 'practices', 'retrieves', 'assesses'] as const
    for (const role of roles) {
      const learning = minimalPuzzle().learning
      expect(() => buildCatalog({
        ...minimalSource(),
        puzzles: [minimalPuzzle({
          learning: { ...learning, [role]: [performanceId('missing')] },
        })],
      })).toThrow(/unknown performance/)
      expect(() => buildCatalog({
        ...minimalSource(),
        puzzles: [minimalPuzzle({
          learning: { ...learning, [role]: [fixturePerformanceId, fixturePerformanceId] },
        })],
      })).toThrow(/duplicate.*learning role/)
    }
  })

  it('accepts a reachable canonical recognized-unwinnable teacher intervention', () => {
    expect(() => buildCatalog({ ...minimalSource(), puzzles: [fourPuzzle] })).not.toThrow()
  })

  it('rejects duplicate, blank, and unknown teacher intervention metadata', () => {
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [reachedTwoVeils, reachedTwoVeils],
      })],
    })).toThrow(/duplicate.*teacher intervention/)
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{ ...reachedTwoVeils, id: ' ' }],
      })],
    })).toThrow(/teacher intervention.*id/)
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{ ...reachedTwoVeils, text: '' }],
      })],
    })).toThrow(/teacher intervention.*text/)
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{ ...reachedTwoVeils, performance: performanceId('missing') }],
      })],
    })).toThrow(/teacher intervention.*unknown performance/)
  })

  it('rejects malformed or unreachable recognized-unwinnable teacher triggers', () => {
    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{
          ...reachedTwoVeils,
          trigger: { ...reachedTwoVeils.trigger, demonstration: [] },
        }],
      })],
    })).toThrow(/unwinnable-state demonstration.*nonempty/)

    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{
          ...reachedTwoVeils,
          trigger: {
            ...reachedTwoVeils.trigger,
            state: { diagram: twoVeils().goal.diagram, boundary: ['open-wire'] },
          },
        }],
      })],
    })).toThrow(/closed/)

    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{
          ...reachedTwoVeils,
          trigger: {
            ...reachedTwoVeils.trigger,
            state: { diagram: blankDiagram(), boundary: [] },
          },
        }],
      })],
    })).toThrow(/canonical blank.*completion owns that event/)

    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [minimalPuzzle({
        teacher: [{
          ...reachedTwoVeils,
          trigger: {
            ...reachedTwoVeils.trigger,
            demonstration: [{ rule: 'doubleCutElim' as const, region: 'missing-region' }],
          },
        }],
      })],
    })).toThrow()

    expect(() => buildCatalog({
      ...minimalSource(), puzzles: [fourPuzzle, {
        ...fourPuzzle,
        id: puzzleId('mismatched-state'),
        teacher: [{
          ...reachedTwoVeils,
          trigger: { ...reachedTwoVeils.trigger, state: four.goal },
        }],
      }],
    })).toThrow(/demonstration does not reach its declared unwinnable state/)
  })

  it('verifies theorem witnesses only against completed prerequisites', () => {
    const prerequisite = minimalPuzzle({ id: puzzleId('prerequisite-artifact') })
    const theoremWitness = {
      rule: 'theorem' as const,
      name: artifactTheoremName(prerequisite.id),
      direction: 'reverse' as const,
      at: {
        sel: {
          region: prerequisite.goal.diagram.root,
          regions: [fixture.eliminations[0]!],
          nodes: [],
          wires: [],
        },
        args: [],
      },
    }
    const dependent = minimalPuzzle({
      id: puzzleId('dependent-artifact'),
      prerequisites: [prerequisite.id],
      witness: [theoremWitness],
      learning: { ...minimalPuzzle().learning, rulesUsed: ['theorem'] },
    })
    const validSource = {
      ...minimalSource(),
      cultures: [{ ...culture, gateway: prerequisite.id }],
      puzzles: [dependent, prerequisite],
    }

    expect(() => buildCatalog(validSource)).not.toThrow()
    expect(() => buildCatalog({
      ...validSource,
      puzzles: [{
        ...dependent,
        prerequisites: [],
        witness: [{ ...theoremWitness, name: artifactTheoremName(dependent.id) }],
      }, prerequisite],
    })).toThrow(/unknown theorem/)
  })

  it('requires declared rules to exactly equal witness rules', () => {
    const learning = minimalPuzzle().learning
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({ learning: { ...learning, rulesUsed: [] } })],
    })).toThrow(/rulesUsed.*witness/)
    expect(() => buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({ learning: { ...learning, rulesUsed: ['doubleCutIntro'] } })],
    })).toThrow(/rulesUsed.*witness/)
  })

  it('excludes artifact, culture, and teacher prose from each puzzle logical fingerprint', () => {
    const original = buildCatalog(minimalSource())
    const changedTeacher = buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({
        teacher: [{
          id: 'opening-pair', performance: fixturePerformanceId,
          trigger: { kind: 'opening' }, text: 'Changed teacher copy.', repeat: 'once',
        }],
      })],
    })
    const changedHistory = buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, historicalSummary: 'Changed cultural history.' }],
    })

    const changedArtifact = buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({
        name: { professional: 'Renamed artifact' },
        provenance: { summary: 'Changed provenance.', function: 'Changed function.' },
      })],
    })

    expect(changedTeacher.puzzleFingerprint(puzzle.id)).toBe(original.puzzleFingerprint(puzzle.id))
    expect(changedHistory.puzzleFingerprint(puzzle.id)).toBe(original.puzzleFingerprint(puzzle.id))
    expect(changedArtifact.puzzleFingerprint(puzzle.id)).toBe(original.puzzleFingerprint(puzzle.id))
  })

  it('fingerprints canonical goal, prerequisite availability, relation logic, and witness replay data', () => {
    const other = fourVeils().goal
    const withRelations = (relations: ReadonlyMap<string, typeof fixture.goal>) => buildCatalog({
      ...minimalSource(), context: { relations },
    })

    const original = withRelations(new Map([['alpha', fixture.goal], ['beta', other]]))
    const reordered = withRelations(new Map([['beta', other], ['alpha', fixture.goal]]))
    const changed = withRelations(new Map([['alpha', fixture.goal], ['beta', fixture.goal]]))

    const changedGoalFixture = fourVeils()
    const changedGoal = buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({
        goal: changedGoalFixture.goal,
        witness: changedGoalFixture.eliminations.map((region) => ({
          rule: 'doubleCutElim' as const,
          region,
        })),
      })],
    })
    const prerequisite = minimalPuzzle({ id: puzzleId('logical-prerequisite') })
    const withPrerequisite = buildCatalog({
      ...minimalSource(),
      cultures: [{ ...culture, gateway: prerequisite.id }],
      puzzles: [prerequisite, minimalPuzzle({ prerequisites: [prerequisite.id] })],
    })
    const reversedWitness = buildCatalog({
      ...minimalSource(),
      puzzles: [minimalPuzzle({
        goal: changedGoalFixture.goal,
        witness: [...changedGoalFixture.eliminations].reverse().map((region) => ({
          rule: 'doubleCutElim' as const,
          region,
        })),
      })],
    })

    expect(reordered.puzzleFingerprint(puzzle.id)).toBe(original.puzzleFingerprint(puzzle.id))
    expect(changed.puzzleFingerprint(puzzle.id)).not.toBe(original.puzzleFingerprint(puzzle.id))
    expect(changedGoal.puzzleFingerprint(puzzle.id)).not.toBe(original.puzzleFingerprint(puzzle.id))
    expect(withPrerequisite.puzzleFingerprint(puzzle.id)).not.toBe(original.puzzleFingerprint(puzzle.id))
    expect(reversedWitness.puzzleFingerprint(puzzle.id))
      .not.toBe(changedGoal.puzzleFingerprint(puzzle.id))
  })

  it('owns one immutable snapshot independent of every caller alias', () => {
    const mutableGoalFixture = twoVeils()
    const mutableRelationFixture = fourVeils()
    const mutableCulture = { ...culture }
    const cultures = [mutableCulture]
    const prerequisites: PuzzleId[] = []
    const witness = [{ rule: 'doubleCutElim' as const, region: mutableGoalFixture.eliminations[0]! }]
    const mutablePuzzle = {
      ...puzzle, name: { ...puzzle.name }, goal: mutableGoalFixture.goal, prerequisites, witness,
    }
    const puzzles = [mutablePuzzle]
    const relationDefinition = { diagram: mutableRelationFixture.goal.diagram, boundary: [] as string[] }
    const relations = new Map([['veil', relationDefinition]])
    const context = { relations }
    const performances = [minimalPerformance()]
    const source = { cultures, performances, puzzles, context }
    const originalPuzzleName = { ...puzzle.name }
    const originalGoalForm = exploreForm(mutableGoalFixture.goal.diagram)
    const originalRelationForm = exploreForm(mutableRelationFixture.goal.diagram)
    const catalog = buildCatalog(source)
    const fingerprint = catalog.fingerprint

    mutableCulture.name = 'Mutated culture'
    cultures.push({
      ...culture, id: cultureId('intruder'), name: 'Intruder', relativeAge: 1,
    })
    mutablePuzzle.id = puzzleId('mutated-puzzle')
    mutablePuzzle.culture = cultureId('mutated-culture')
    mutablePuzzle.name.professional = 'Mutated puzzle'
    mutablePuzzle.goal = fourVeils().goal
    prerequisites.push(puzzleId('missing'))
    witness.length = 0
    puzzles.splice(0, 1)
    const goalOuter = mutableGoalFixture.eliminations[0]!
    const mutableGoalRegion = mutableGoalFixture.goal.diagram.regions[goalOuter] as { parent: string }
    mutableGoalRegion.parent = 'mutated-parent'
    const relationOuter = mutableRelationFixture.eliminations[0]!
    const mutableRelationRegion = mutableRelationFixture.goal.diagram.regions[relationOuter] as { parent: string }
    mutableRelationRegion.parent = 'mutated-parent'
    relationDefinition.boundary.push('missing-wire')
    relations.clear()
    context.relations = new Map([['replacement', { diagram: fourVeils().goal.diagram, boundary: [] }]])

    expect(catalog.fingerprint).toBe(fingerprint)
    expect(catalog.source.cultures).toHaveLength(1)
    expect(catalog.source.cultures[0]?.name).toBe(culture.name)
    expect(catalog.source.puzzles).toHaveLength(1)
    expect(catalog.puzzle(puzzle.id)).toMatchObject({
      name: originalPuzzleName,
      prerequisites: [],
    })
    expect(catalog.puzzle(puzzle.id).witness).toHaveLength(1)
    expect(exploreForm(catalog.puzzle(puzzle.id).goal.diagram)).toBe(originalGoalForm)
    expect([...catalog.source.context.relations.keys()]).toEqual(['veil'])
    expect(catalog.source.context.relations.get('veil')?.boundary).toEqual([])
    expect(exploreForm(catalog.source.context.relations.get('veil')!.diagram)).toBe(originalRelationForm)
    const ownedPuzzle = catalog.puzzle(puzzle.id)
    const authority = {
      context: { ...catalog.source.context, theorems: new Map() },
    }
    let session = startPuzzle(ownedPuzzle)
    for (const step of ownedPuzzle.witness) session = applyGameStep(session, step, authority).session
    expect(isBlank(currentDiagram(session))).toBe(true)
    const controller = reduceGame(
      catalog,
      createInitialGameState(catalog, { reducedMotion: false }),
      { kind: 'selectPuzzle', puzzle: puzzle.id },
    ).state
    const save = encodeGameSave(catalog, controller)
    expect(save.puzzleFingerprints).toEqual({ [puzzle.id]: catalog.puzzleFingerprint(puzzle.id) })
    const loaded = decodeGameSave(catalog, save)
    expect(exploreForm(currentDiagram(loaded.firstAttempts.get(puzzle.id)!)))
      .toBe(originalGoalForm)

    expect(() => (catalog.source.cultures as CultureDefinition[]).push(mutableCulture)).toThrow()
    expect(() => (catalog.source.puzzles as PuzzleDefinition[]).push(mutablePuzzle)).toThrow()
    expect(() => (catalog.source.context.relations as Map<string, typeof fixture.goal>)
      .set('mutated', fixture.goal)).toThrow()
  })
})
