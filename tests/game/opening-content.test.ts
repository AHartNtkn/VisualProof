import { describe, expect, it } from 'vitest'
import seyricCoverage from '../../content/coverage/seyric.json'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content'
import { analyzeSeyricStart } from '../../src/game/content/seyric-authority'
import { puzzleId } from '../../src/game/types'

const catalog = loadGameContent(gameContentFiles)
const onboardingIds = [
  'two-veils',
  'four-veils',
  'forked-veil',
  'echoed-veil',
] as const
const nestedOwnerRootIds = [
  'transfer-duplication-recognition',
  'common-conjunction-factor-base',
  'common-disjunction-factor-base',
  'disjunction-over-conjunction-base',
  'i-dao',
  'two-mark-projection',
  'left-injection-introduction',
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
  'sey-pei-i01',
  'weakening-injection-weave',
  'b3',
  'de-morgan-product-consumer',
  'de-morgan-sum-consumer',
  'double-cut-copy-license',
  'preserve-sole-structural-source',
  'r4',
  'r5',
  'recollect-shared-branch-context',
  'seyric-field-edit-contrast',
  'seyric-extraction-continuation',
] as const
const reconstructedPrerequisites = [
  ['atomic-fragment-erasure', ['compound-weakening-boundary']],
  ['atomic-content-insertion', ['marked-echo-deiteration']],
  ['polarity-bubble-contrast', ['marked-echo-deiteration']],
  ['seyric-compound-copy-authority', ['marked-echo-deiteration']],
  ['seyric-atomic-double-cut-selection', ['marked-echo-deiteration']],
  ['compound-double-cut-selection', ['seyric-atomic-double-cut-selection']],
  ['content-bearing-annulus-choice', ['compound-double-cut-selection']],
  ['double-cut-insertion-workspace', ['seyric-atomic-double-cut-selection', 'atomic-content-insertion']],
  ['compound-weakening-boundary', ['two-mark-projection']],
  ['sey-red-c01', ['nested-owner-introduction']],
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

  it('keeps the early cut exercises mark-free and introduces the Seyric empty-owner exercise', () => {
    for (const id of onboardingIds) {
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
    expect(catalog.placement(puzzleId('empty-ring-release')).prerequisites)
      .toEqual([puzzleId('echoed-veil')])
    expect(catalog.placement(puzzleId('single-mark-return')).prerequisites)
      .toEqual([puzzleId('empty-ring-release')])
    expect(catalog.placement(puzzleId('nested-owner-introduction')).prerequisites)
      .toEqual([puzzleId('single-mark-return')])

    for (const id of nestedOwnerRootIds) {
      expect(catalog.placement(puzzleId(id)).prerequisites)
        .toEqual([puzzleId('nested-owner-introduction')])
    }
    for (const id of ['conjunction-idempotence-introduction', 'disjunction-idempotence-introduction']) {
      expect(catalog.placement(puzzleId(id)).prerequisites)
        .toEqual([puzzleId('single-mark-return')])
    }
    for (const [id, prerequisites] of reconstructedPrerequisites) {
      expect(catalog.placement(puzzleId(id)).prerequisites)
        .toEqual(prerequisites.map(puzzleId))
    }
  })

  it('introduces marked ancestor-supported deiteration after the first marked problem', () => {
    const id = puzzleId('marked-echo-deiteration')
    const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
    expect(seyric.indexOf(id)).toBeGreaterThan(seyric.indexOf(puzzleId('nested-owner-introduction')))
    expect(catalog.placement(id).prerequisites).toEqual([puzzleId('nested-owner-introduction')])

    const diagram = catalog.puzzle(id).diagram
    const start = analyzeSeyricStart(diagram)
    expect(start.prefix).toHaveLength(3)
    expect(start.matrixRoot).not.toBeNull()
    expect(Object.values(diagram.nodes).filter(({ kind }) => kind === 'atom')).toHaveLength(6)
    expect(new Set(Object.values(diagram.nodes).flatMap((node) =>
      node.kind === 'atom' ? [node.binder] : []))).toEqual(new Set(start.prefix))
  })

  it('keeps every Seyric start propositional and canonically distinct', () => {
    const violations: string[] = []
    const idsByFingerprint = new Map<string, string[]>()

    for (const id of catalog.puzzlesInCulture('seyric-horizon' as never)) {
      const diagram = catalog.puzzle(id).diagram
      violations.push(...analyzeSeyricStart(diagram).violations.map(({ code, detail }) =>
        `${id} [${code}]: ${detail}`))

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

  it('keeps blank-witness as the Myratic gateway ahead of optional Myratic practice', () => {
    expect(catalog.cultureIds).toEqual(['seyric-horizon', 'myratic-tradition'])
    expect(catalog.puzzlesInCulture('myratic-tradition' as never)).toEqual([
      'blank-witness',
      'useful-vacuous-owner-workspace',
      'shallow-edit-legality-contrast',
      'compound-copy-authority-contrast',
      'atomic-double-cut-selection',
      'rm-c3',
      'sey-ref-sel-i01',
      'compound-theorem-source-choice',
      'useful-manifestation-target',
      'sey-ref-dis-i01',
      'compound-context-dissolution',
      'artifact-creates-copy-authority',
      'artifact-polarity-direction-contrast',
      'artifact-preserves-copy-authority',
      'artifact-selected-downstream-bridge',
    ])
    expect(catalog.culture('myratic-tradition' as never)).toMatchObject({
      gateway: 'blank-witness',
      unlocksAfter: ['nested-owner-introduction'],
    })
    expect(catalog.placement(puzzleId('blank-witness'))).toEqual({
      puzzle: 'blank-witness', culture: 'myratic-tradition', prerequisites: [],
    })
    expect(catalog.placement(puzzleId('empty-ring-release'))).toEqual({
      puzzle: 'empty-ring-release', culture: 'seyric-horizon',
      prerequisites: [puzzleId('echoed-veil')],
    })

    const blankWitness = catalog.puzzle(puzzleId('blank-witness')).diagram
    expect(Object.keys(blankWitness.nodes)).toHaveLength(1)
    expect(Object.values(blankWitness.regions).filter(({ kind }) => kind === 'bubble')).toEqual([
      expect.objectContaining({ kind: 'bubble', arity: 0 }),
    ])
  })
})
