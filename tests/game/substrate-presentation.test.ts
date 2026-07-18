import { describe, expect, it } from 'vitest'
import { buildCatalog } from '../../src/game/catalog'
import {
  EMPTY_ARCHIVE_SUBSTRATE_SEED,
  puzzleSubstrateSeed,
  substratePresentation,
} from '../../src/game/interface/substrate-presentation'
import { minimalSource } from './catalog-fixture'

describe('deterministic substrate presentation', () => {
  it('is identical for an identical explicit seed and restrained in every channel', () => {
    const first = substratePresentation(EMPTY_ARCHIVE_SUBSTRATE_SEED)
    const second = substratePresentation(EMPTY_ARCHIVE_SUBSTRATE_SEED)
    expect(first).toEqual(second)
    expect(Math.abs(first.rotationDegrees)).toBeLessThanOrEqual(0.9)
    expect(Math.abs(first.hueDegrees)).toBeLessThanOrEqual(5)
    expect(first.saturation).toBeGreaterThanOrEqual(0.94)
    expect(first.saturation).toBeLessThanOrEqual(1.06)
  })

  it('uses logical puzzle identity rather than catalog presentation prose', () => {
    const source = minimalSource()
    const original = buildCatalog(source)
    const rewritten = buildCatalog({
      ...source,
      puzzles: source.puzzles.map((puzzle) => ({
        ...puzzle,
        name: { professional: 'Completely revised catalog label' },
        provenance: { summary: 'New catalog prose.', function: 'New interpretation.' },
      })),
    })
    const id = source.puzzles[0]!.id
    expect(puzzleSubstrateSeed(original, id)).toBe(puzzleSubstrateSeed(rewritten, id))
    expect(substratePresentation(puzzleSubstrateSeed(original, id))).toEqual(
      substratePresentation(puzzleSubstrateSeed(rewritten, id)),
    )
  })

  it('demonstrably varies crop, rotation, and tint across puzzle seeds', () => {
    const presentations = ['first:0001', 'second:0002', 'third:0003']
      .map(substratePresentation)
    expect(new Set(presentations.map(({ positionX }) => positionX)).size).toBeGreaterThan(1)
    expect(new Set(presentations.map(({ rotationDegrees }) => rotationDegrees)).size)
      .toBeGreaterThan(1)
    expect(new Set(presentations.map(({ hueDegrees }) => hueDegrees)).size).toBeGreaterThan(1)
  })
})
