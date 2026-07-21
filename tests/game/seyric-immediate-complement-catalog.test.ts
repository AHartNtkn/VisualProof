import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content/files'
import { analyzeSeyricPropositionalShape } from '../../src/game/content/seyric-authority'

const approvedExactStarts = [
  'echoed-veil',
  'single-mark-return',
  'nested-owner-introduction',
  'compound-weakening-boundary',
  'two-mark-projection',
  'compound-projection',
  'ternary-projection-choice',
  'atomic-conjunction-exchange',
  'compound-conjunction-exchange',
  'disjunction-exchange-recognition',
  'conjunction-reassociation-recognition',
  'disjunction-reassociation-recognition',
  'i-aa',
  'b6',
  'sey-red-c01',
] as const

type CoverageFile = {
  readonly puzzles: readonly {
    readonly puzzle: string
    readonly immediateComplementPattern?: string
  }[]
}

describe('Seyric exact immediate-complement catalog', () => {
  it('contains exactly the independently reviewed graphical-recognition starts', () => {
    const catalog = loadGameContent(gameContentFiles)
    const detected = catalog.puzzlesInCulture('seyric-horizon' as never)
      .filter((id) => analyzeSeyricPropositionalShape(catalog.puzzle(id).diagram).immediateComplement)

    expect(detected).toEqual(approvedExactStarts)
  })

  it('classifies every approved start once and no other start', () => {
    const coverage = JSON.parse(readFileSync(
      resolve(process.cwd(), 'content/coverage/seyric.json'),
      'utf8',
    )) as CoverageFile
    const classified = coverage.puzzles
      .filter((row) => row.immediateComplementPattern !== undefined)

    expect(classified.map((row) => row.puzzle)).toEqual(approvedExactStarts)
    expect(new Set(classified.map((row) => row.immediateComplementPattern)).size)
      .toBe(classified.length)
  })
})
