import { describe, expect, it } from 'vitest'
import seyricCoverage from '../../content/coverage/seyric.json'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content'
import { cutDepth } from '../../src/kernel/diagram'
import { puzzleId } from '../../src/game/types'

const catalog = loadGameContent(gameContentFiles)
const onboardingIds = [
  'two-veils',
  'four-veils',
  'forked-veil',
  'echoed-veil',
  'empty-ring-release',
] as const
const singleMarkRootIds = [
  'atomic-fragment-erasure',
  'compound-copy-authority-contrast',
  'transfer-duplication-recognition',
  'common-conjunction-factor-base',
  'common-disjunction-factor-base',
  'content-bearing-annulus-choice',
  'disjunction-over-conjunction-base',
  'i-dao',
  'conjunction-idempotence-introduction',
  'weakening-introduction',
  'two-mark-projection',
  'left-injection-introduction',
  'disjunction-idempotence-introduction',
  'atomic-conjunction-exchange',
  'disjunction-exchange-recognition',
  'conjunction-reassociation-recognition',
  'disjunction-reassociation-recognition',
  'i-c3',
  'i-cs',
  'i-al',
  'i-case2',
  'i-om',
  'i-aa',
  'i-ao',
  'sey-ctr-i01',
  'sey-dm-ec-i01',
  'sey-dm-fc-i01',
  'sey-red-i01',
  'sey-pei-i01',
  'weakening-injection-weave',
  'b3',
  'de-morgan-product-consumer',
  'de-morgan-sum-consumer',
  'double-cut-copy-license',
  'double-cut-insertion-workspace',
  'preserve-sole-structural-source',
  'r4',
  'r5',
  'recollect-shared-branch-context',
  'rm-c3',
] as const
const reconstructedPrerequisites = [
  ['shallow-edit-legality-contrast', 'single-mark-return'],
  ['atomic-content-insertion', 'marked-echo-deiteration'],
  ['atomic-double-cut-selection', 'marked-echo-deiteration'],
  ['polarity-bubble-contrast', 'marked-echo-deiteration'],
] as const
describe('reconstructed opening content', () => {
  it('matches the accepted Seyric collection structurally without making its count authoritative', () => {
    const acceptedIds = seyricCoverage.puzzles.map(({ puzzle }) => puzzle).sort()
    const seyricIds = [...catalog.puzzlesInCulture('seyric-horizon' as never)].sort()

    expect(seyricIds).toEqual(acceptedIds)
    expect(catalog.puzzleIds).toEqual(
      catalog.cultureIds.flatMap((culture) => catalog.puzzlesInCulture(culture)),
    )
  })

  it('keeps the early cut exercises mark-free and introduces one empty ring afterward', () => {
    for (const id of onboardingIds.slice(0, 4)) {
      const diagram = catalog.puzzle(puzzleId(id)).diagram
      expect(Object.values(diagram.regions).every(({ kind }) => kind !== 'bubble')).toBe(true)
      expect(Object.keys(diagram.nodes)).toEqual([])
      expect(Object.keys(diagram.wires)).toEqual([])
    }

    const ring = catalog.puzzle(puzzleId('empty-ring-release')).diagram
    expect(Object.values(ring.regions).filter(({ kind }) => kind === 'bubble')).toEqual([
      expect.objectContaining({ kind: 'bubble', arity: 0 }),
    ])
    expect(Object.keys(ring.nodes)).toEqual([])
    expect(Object.keys(ring.wires)).toEqual([])
  })

  it('attaches each opening practice problem behind its required concept', () => {
    expect(catalog.placement(puzzleId('two-veils')).prerequisites).toEqual([])
    expect(catalog.placement(puzzleId('four-veils')).prerequisites).toEqual([puzzleId('two-veils')])
    expect(catalog.placement(puzzleId('forked-veil')).prerequisites).toEqual([puzzleId('two-veils')])
    expect(catalog.placement(puzzleId('echoed-veil')).prerequisites).toEqual([puzzleId('forked-veil')])
    expect(catalog.placement(puzzleId('empty-ring-release')).prerequisites).toEqual([puzzleId('echoed-veil')])
    expect(catalog.placement(puzzleId('single-mark-return')).prerequisites)
      .toEqual([puzzleId('empty-ring-release')])

    for (const id of singleMarkRootIds) {
      expect(catalog.placement(puzzleId(id)).prerequisites)
        .toEqual([puzzleId('single-mark-return')])
    }
    for (const [id, prerequisite] of reconstructedPrerequisites) {
      expect(catalog.placement(puzzleId(id)).prerequisites)
        .toEqual([puzzleId(prerequisite)])
    }
  })

  it('introduces marked ancestor-supported deiteration after mark ownership', () => {
    const id = puzzleId('marked-echo-deiteration')
    const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
    expect(seyric.indexOf(id)).toBe(seyric.indexOf(puzzleId('single-mark-return')) + 1)
    expect(catalog.placement(id).prerequisites).toEqual([puzzleId('single-mark-return')])

    const diagram = catalog.puzzle(id).diagram
    expect(Object.values(diagram.regions).filter(({ kind }) => kind === 'bubble')).toHaveLength(1)
    expect(Object.values(diagram.nodes).filter(({ kind }) => kind === 'atom')).toHaveLength(2)
  })

  it('keeps every Seyric start propositional and canonically distinct', () => {
    const violations: string[] = []
    const idsByFingerprint = new Map<string, string[]>()

    for (const id of catalog.puzzlesInCulture('seyric-horizon' as never)) {
      const diagram = catalog.puzzle(id).diagram
      for (const [regionId, region] of Object.entries(diagram.regions)) {
        if (region.kind !== 'bubble') continue
        if (region.arity !== 0) violations.push(`${id}: bubble '${regionId}' has arity ${region.arity}`)
        if (cutDepth(diagram, regionId) % 2 === 0) {
          violations.push(`${id}: bubble '${regionId}' is existential`)
        }
      }
      for (const [nodeId, node] of Object.entries(diagram.nodes)) {
        if (node.kind !== 'atom') violations.push(`${id}: node '${nodeId}' has kind '${node.kind}'`)
      }
      if (Object.keys(diagram.wires).length > 0) violations.push(`${id}: contains individual wires`)

      const fingerprint = catalog.puzzleFingerprint(id)
      idsByFingerprint.set(fingerprint, [...(idsByFingerprint.get(fingerprint) ?? []), id])
    }

    expect(violations).toEqual([])
    expect([...idsByFingerprint.values()].filter((ids) => ids.length > 1)).toEqual([])
  })

  it('preserves progression, artifact, and optional guidance as separate ownership layers', () => {
    const first = puzzleId('single-mark-return')
    expect(catalog.placement(first)).toEqual({
      puzzle: first, culture: 'seyric-horizon', prerequisites: [puzzleId('empty-ring-release')],
    })
    expect(catalog.artifact(first).name).toEqual({
      professional: 'The Auten Reliquary Closure',
      curatorShorthand: 'single-ring ownership form',
    })
    expect(catalog.guidance(first).interventions[0]?.pages).toHaveLength(4)
    expect(catalog.guidance(puzzleId('two-mark-projection')).interventions).toEqual([])
  })

  it('preserves the Myratic blank-witness outside the Seyric reconstruction', () => {
    expect(catalog.cultureIds).toEqual(['seyric-horizon', 'myratic-tradition'])
    expect(catalog.puzzlesInCulture('myratic-tradition' as never)).toEqual(['blank-witness'])
    expect(catalog.culture('myratic-tradition' as never)).toMatchObject({
      gateway: 'blank-witness',
      unlocksAfter: ['single-mark-return'],
    })
    expect(catalog.placement(puzzleId('blank-witness'))).toEqual({
      puzzle: 'blank-witness', culture: 'myratic-tradition', prerequisites: [],
    })

    const blankWitness = catalog.puzzle(puzzleId('blank-witness')).diagram
    expect(Object.keys(blankWitness.nodes)).toHaveLength(1)
    expect(Object.values(blankWitness.regions).filter(({ kind }) => kind === 'bubble')).toEqual([
      expect.objectContaining({ kind: 'bubble', arity: 0 }),
    ])
  })
})
