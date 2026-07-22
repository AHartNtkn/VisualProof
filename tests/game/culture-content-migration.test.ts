import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import myraticCoverage from '../../content/coverage/myratic.json'
import seyricCoverage from '../../content/coverage/seyric.json'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { puzzleId } from '../../src/game/types'

const myraticOwned = [
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
] as const

const expectedMyraticOrder = [
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
] as const

const expectedMyraticPrerequisites: Record<(typeof myraticOwned)[number], readonly string[]> = {
  'useful-vacuous-owner-workspace': ['blank-witness', 'empty-ring-release', 'marked-echo-deiteration'],
  'shallow-edit-legality-contrast': ['blank-witness', 'single-mark-return'],
  'compound-copy-authority-contrast': ['blank-witness', 'marked-echo-deiteration'],
  'atomic-double-cut-selection': ['blank-witness', 'marked-echo-deiteration'],
  'rm-c3': ['blank-witness', 'single-mark-return'],
  'sey-ref-sel-i01': ['blank-witness', 'single-mark-return', 'nested-owner-introduction'],
  'compound-theorem-source-choice': ['blank-witness', 'sey-lem-i01', 'sey-lem-c01', 'sey-ref-sel-i01'],
  'useful-manifestation-target': ['blank-witness', 'two-mark-projection'],
  'sey-ref-dis-i01': ['blank-witness', 'single-mark-return'],
  'compound-context-dissolution': ['blank-witness', 'rm-fa', 'sey-ref-dis-i01'],
  'artifact-creates-copy-authority': ['blank-witness', 'single-mark-return'],
  'artifact-polarity-direction-contrast': ['blank-witness', 'two-mark-projection'],
  'artifact-preserves-copy-authority': ['blank-witness', 'single-mark-return'],
  'artifact-selected-downstream-bridge': ['blank-witness', 'i-c3', 'i-c4'],
}

const seyricOwnedAdditions = [
  'seyric-field-edit-contrast',
  'seyric-compound-copy-authority',
  'seyric-atomic-double-cut-selection',
  'seyric-extraction-continuation',
] as const

const removed = ['weakening-introduction', 'sey-red-i01'] as const

const catalog = loadGameContent(gameContentFiles)

describe('culture ownership migration', () => {
  it('owns the gateway and local-scope practice in Myratic in coherent order', () => {
    expect(catalog.culture('myratic-tradition' as never)).toMatchObject({
      gateway: 'blank-witness',
      unlocksAfter: ['nested-owner-introduction'],
    })
    expect(catalog.puzzlesInCulture('myratic-tradition' as never)).toEqual(expectedMyraticOrder)
    expect(catalog.puzzlesInCulture('seyric-horizon' as never))
      .not.toEqual(expect.arrayContaining([...myraticOwned]))
  })

  it('makes every local-scope record optional Myratic practice behind blank-witness', () => {
    for (const id of myraticOwned) {
      expect(catalog.placement(puzzleId(id))).toEqual({
        puzzle: id,
        culture: 'myratic-tradition',
        prerequisites: expectedMyraticPrerequisites[id],
      })
    }
    expect(catalog.placement(puzzleId('blank-witness'))).toEqual({
      puzzle: 'blank-witness',
      culture: 'myratic-tradition',
      prerequisites: [],
    })
  })

  it('keeps the minimal Seyric closure and integrates the culture-owned additions', () => {
    expect(catalog.placement(puzzleId('two-veils')).prerequisites).toEqual([])
    expect(catalog.placement(puzzleId('forked-veil')).prerequisites).toEqual([puzzleId('two-veils')])
    expect(catalog.placement(puzzleId('echoed-veil')).prerequisites).toEqual([puzzleId('forked-veil')])
    expect(catalog.placement(puzzleId('empty-ring-release')).prerequisites).toEqual([puzzleId('echoed-veil')])
    expect(catalog.placement(puzzleId('single-mark-return')).prerequisites)
      .toEqual([puzzleId('empty-ring-release')])
    expect(catalog.placement(puzzleId('nested-owner-introduction')).prerequisites)
      .toEqual([puzzleId('single-mark-return')])
    expect(catalog.placement(puzzleId('four-veils')).prerequisites).toEqual([puzzleId('two-veils')])

    expect(catalog.puzzlesInCulture('seyric-horizon' as never)).toEqual(expect.arrayContaining([...seyricOwnedAdditions]))
    const seyric = catalog.puzzlesInCulture('seyric-horizon' as never)
    expect(seyric.indexOf(puzzleId('seyric-field-edit-contrast')))
      .toBe(seyric.indexOf(puzzleId('marked-echo-deiteration')) + 1)
    expect(seyric.indexOf(puzzleId('seyric-compound-copy-authority')))
      .toBe(seyric.indexOf(puzzleId('atomic-content-insertion')) + 1)
    expect(seyric.indexOf(puzzleId('seyric-atomic-double-cut-selection')))
      .toBe(seyric.indexOf(puzzleId('transfer-duplication-recognition')) + 1)
    expect(seyric.indexOf(puzzleId('seyric-extraction-continuation')))
      .toBe(seyric.indexOf(puzzleId('recollect-shared-branch-context')) + 1)
    expect(catalog.placement(puzzleId('seyric-field-edit-contrast')).prerequisites)
      .toEqual([puzzleId('nested-owner-introduction')])
    expect(catalog.placement(puzzleId('seyric-compound-copy-authority')).prerequisites)
      .toEqual([puzzleId('marked-echo-deiteration')])
    expect(catalog.placement(puzzleId('seyric-atomic-double-cut-selection')).prerequisites)
      .toEqual([puzzleId('marked-echo-deiteration')])
    expect(catalog.placement(puzzleId('seyric-extraction-continuation')).prerequisites)
      .toEqual([puzzleId('nested-owner-introduction')])
    expect(catalog.placement(puzzleId('compound-double-cut-selection')).prerequisites)
      .toEqual([puzzleId('seyric-atomic-double-cut-selection')])
    expect(catalog.placement(puzzleId('double-cut-insertion-workspace')).prerequisites)
      .toEqual([puzzleId('seyric-atomic-double-cut-selection'), puzzleId('atomic-content-insertion')])
  })

  it('deletes the redundant records and rewires every named dependent or neighbor', () => {
    const allAuthorityText = [
      'content/manifest.json',
      'content/progression/core.json',
      'content/catalog/cursebreaker.json',
      'content/guidance/cursebreaker.json',
      'content/coverage/seyric.json',
      'content/coverage/myratic.json',
    ].map((path) => readFileSync(resolve(process.cwd(), path), 'utf8')).join('\n')
    for (const id of removed) {
      expect(allAuthorityText, id).not.toContain(id)
      expect(gameContentFiles).not.toHaveProperty(`puzzles/${id}.json`)
    }
    expect(catalog.placement(puzzleId('compound-weakening-boundary')).prerequisites)
      .toEqual([puzzleId('two-mark-projection')])
    expect(catalog.placement(puzzleId('sey-red-c01')).prerequisites)
      .toEqual([puzzleId('nested-owner-introduction')])

    const coverageRow = seyricCoverage.puzzles.find(({ puzzle }) =>
      puzzle === 'assumption-relevant-structured-reductio')
    expect(coverageRow?.experientialNeighbors).toContain('sey-red-c01')
    expect(coverageRow?.experientialNeighbors).not.toContain('sey-red-i01')
  })

  it('moves and splits culture-owned coverage without dangling rows', () => {
    const seyricRows = new Map(seyricCoverage.puzzles.map((row) => [row.puzzle, row]))
    const myraticRows = new Map(myraticCoverage.puzzles.map((row) => [row.puzzle, row]))
    for (const id of myraticOwned) {
      expect(seyricRows.has(id), id).toBe(false)
      expect(myraticRows.has(id), id).toBe(true)
    }
    for (const id of ['empty-ring-release', 'nested-owner-introduction'] as const) {
      expect(seyricRows.has(id), id).toBe(true)
      expect(myraticRows.has(id), id).toBe(false)
    }

    expect(myraticRows.get('shallow-edit-legality-contrast')?.obligations)
      .toEqual(['interaction-host-scope-edit-legality'])
    expect(seyricRows.get('seyric-field-edit-contrast')?.obligations)
      .toEqual(['polarity-shallow-opposite-contrast'])
    expect(myraticRows.get('compound-copy-authority-contrast')?.obligations)
      .toEqual(['myratic-local-owner-copy-authority'])
    expect(seyricRows.get('seyric-compound-copy-authority')?.obligations)
      .toEqual(['iteration-ancestor-descendant-compound', 'interaction-ancestry-copy-authority'])
    expect(myraticRows.get('atomic-double-cut-selection')?.obligations)
      .toEqual(['myratic-local-owner-double-cut-selection'])
    expect(seyricRows.get('seyric-atomic-double-cut-selection')?.obligations)
      .toEqual(['double-cut-introduction-atomic-selection'])
    expect(myraticRows.get('rm-c3')?.obligations)
      .toEqual(['myratic-local-owner-extraction-continuation'])
    expect(seyricRows.get('seyric-extraction-continuation')?.obligations)
      .toEqual(['mixed-extraction-continuation'])

    const seyricObligations = seyricCoverage.obligations.map(({ id }) => id)
    expect(seyricObligations).not.toContain('ownership-vacuous-elimination')
    expect(seyricObligations).not.toContain('weakening-atomic-retained-proposition')
    expect(seyricObligations).not.toContain('reductio-direct-atomic-contradiction')

    const seyricIds = new Set(catalog.puzzlesInCulture('seyric-horizon' as never))
    const myraticIds = new Set(catalog.puzzlesInCulture('myratic-tradition' as never))
    expect(new Set(seyricRows.keys())).toEqual(seyricIds)
    expect(new Set(myraticRows.keys())).toEqual(myraticIds)
  })
})
