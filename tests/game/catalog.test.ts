import { describe, expect, it } from 'vitest'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { buildCatalog } from '../../src/game/catalog'
import { isBlank } from '../../src/game/blank'
import { emptyProgress } from '../../src/game/progress'
import { loadGame, saveGame } from '../../src/game/save'
import { applyGameStep, currentDiagram, startPuzzle } from '../../src/game/session'
import {
  campaignId, GameDomainError, puzzleId,
  type CampaignDefinition, type PuzzleDefinition, type PuzzleId,
} from '../../src/game/types'
import { fourVeils, twoVeils } from './fixtures'

const fixture = twoVeils()
const campaign = { id: campaignId('apprenticeship'), title: 'Curator’s Apprenticeship' }
const puzzle = {
  id: puzzleId('two-veils'), campaign: campaign.id, title: 'Two Veils', goal: fixture.goal,
  prerequisites: [], grantsVellum: true,
  witness: [{ rule: 'doubleCutElim' as const, region: fixture.eliminations[0]! }],
}

describe('verified game catalog', () => {
  it('accepts a closed puzzle whose backward witness reaches blank', () => {
    const catalog = buildCatalog({ campaigns: [campaign], puzzles: [puzzle], context: { relations: new Map() } })
    expect(catalog.puzzle(puzzle.id)).toStrictEqual(puzzle)
    expect(catalog.puzzle(puzzle.id)).not.toBe(puzzle)
  })

  it('rejects missing prerequisites and dependency cycles', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzleId('missing')] }],
    })).toThrow(/missing prerequisite/)
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, prerequisites: [puzzle.id] }],
    })).toThrow(/dependency cycle/)
  })

  it('rejects a witness that does not reach blank', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{ ...puzzle, witness: [] }],
    })).toThrow(/witness does not reach blank/)
  })

  it('rejects a witness that passes through blank and continues', () => {
    expect(() => buildCatalog({
      campaigns: [campaign], context: { relations: new Map() },
      puzzles: [{
        ...puzzle,
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

  it('fingerprints canonical relation content independently of map insertion order', () => {
    const other = fourVeils().goal
    const withRelations = (relations: ReadonlyMap<string, typeof fixture.goal>) => buildCatalog({
      campaigns: [campaign], puzzles: [puzzle], context: { relations },
    })

    const original = withRelations(new Map([['alpha', fixture.goal], ['beta', other]]))
    const reordered = withRelations(new Map([['beta', other], ['alpha', fixture.goal]]))
    const changed = withRelations(new Map([['alpha', fixture.goal], ['beta', fixture.goal]]))

    expect(reordered.fingerprint).toBe(original.fingerprint)
    expect(changed.fingerprint).not.toBe(original.fingerprint)
  })

  it('owns one immutable snapshot independent of every caller alias', () => {
    const mutableGoalFixture = twoVeils()
    const mutableRelationFixture = fourVeils()
    const mutableCampaign = { ...campaign }
    const campaigns = [mutableCampaign]
    const prerequisites: PuzzleId[] = []
    const witness = [{ rule: 'doubleCutElim' as const, region: mutableGoalFixture.eliminations[0]! }]
    const mutablePuzzle = { ...puzzle, goal: mutableGoalFixture.goal, prerequisites, witness }
    const puzzles = [mutablePuzzle]
    const relationDefinition = { diagram: mutableRelationFixture.goal.diagram, boundary: [] as string[] }
    const relations = new Map([['veil', relationDefinition]])
    const context = { relations }
    const source = { campaigns, puzzles, context }
    const originalGoalForm = exploreForm(mutableGoalFixture.goal.diagram)
    const originalRelationForm = exploreForm(mutableRelationFixture.goal.diagram)
    const catalog = buildCatalog(source)
    const fingerprint = catalog.fingerprint

    mutableCampaign.title = 'Mutated campaign'
    campaigns.push({ id: campaignId('intruder'), title: 'Intruder' })
    mutablePuzzle.id = puzzleId('mutated-puzzle')
    mutablePuzzle.campaign = campaignId('mutated-campaign')
    mutablePuzzle.title = 'Mutated puzzle'
    mutablePuzzle.grantsVellum = false
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
    expect(catalog.source.campaigns).toHaveLength(1)
    expect(catalog.source.campaigns[0]?.title).toBe(campaign.title)
    expect(catalog.source.puzzles).toHaveLength(1)
    expect(catalog.puzzle(puzzle.id)).toMatchObject({
      title: puzzle.title,
      grantsVellum: true,
      prerequisites: [],
    })
    expect(catalog.puzzle(puzzle.id).witness).toHaveLength(1)
    expect(exploreForm(catalog.puzzle(puzzle.id).goal.diagram)).toBe(originalGoalForm)
    expect([...catalog.source.context.relations.keys()]).toEqual(['veil'])
    expect(catalog.source.context.relations.get('veil')?.boundary).toEqual([])
    expect(exploreForm(catalog.source.context.relations.get('veil')!.diagram)).toBe(originalRelationForm)
    const ownedPuzzle = catalog.puzzle(puzzle.id)
    const authority = {
      context: catalog.source.context,
      puzzle: (id: PuzzleId) => catalog.puzzle(id),
      canUseVellum: () => false,
    }
    let session = startPuzzle(ownedPuzzle)
    for (const step of ownedPuzzle.witness) session = applyGameStep(session, step, authority).session
    expect(isBlank(currentDiagram(session))).toBe(true)
    const save = saveGame(catalog, emptyProgress(), session)
    expect(save.catalogFingerprint).toBe(fingerprint)
    expect(isBlank(currentDiagram(loadGame(catalog, save).active!))).toBe(true)

    expect(() => (catalog.source.campaigns as CampaignDefinition[]).push(mutableCampaign)).toThrow()
    expect(() => (catalog.source.puzzles as PuzzleDefinition[]).push(mutablePuzzle)).toThrow()
    expect(() => (catalog.source.context.relations as Map<string, typeof fixture.goal>)
      .set('mutated', fixture.goal)).toThrow()
  })
})
