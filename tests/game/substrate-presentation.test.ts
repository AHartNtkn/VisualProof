import { describe, expect, it } from 'vitest'
import {
  EMPTY_ARCHIVE_SUBSTRATE_SEED,
  puzzleSubstrateSeed,
  substratePresentation,
} from '../../src/game/interface/substrate-presentation'
import { puzzleId } from '../../src/game/types'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content'

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
    const original = loadGameContent(gameContentFiles)
    const files = structuredClone(gameContentFiles) as Record<string, unknown>
    const catalog = files['catalog/cursebreaker.json'] as {
      cultures: unknown[]
      artifacts: Array<{ name: { professional: string }; provenance: { summary: string } }>
    }
    catalog.artifacts[0]!.name.professional = 'Completely revised catalog label'
    catalog.artifacts[0]!.provenance.summary = 'New catalog prose.'
    const rewritten = loadGameContent(files)
    const id = puzzleId('single-mark-return')

    expect(puzzleSubstrateSeed(original, id)).toBe(puzzleSubstrateSeed(rewritten, id))
    expect(puzzleSubstrateSeed(original, id)).toMatch(/^cursebreaker:puzzle:single-mark-return:/)
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
