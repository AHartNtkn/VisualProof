import { describe, expect, it } from 'vitest'
import { loadGameContent } from '../../src/game/catalog'
import { gameContentFiles } from '../../src/game/content'
import { requiredPuzzles } from '../../src/game/progress'
import { puzzleId } from '../../src/game/types'

describe('assembled game catalog', () => {
  it('exposes separate ordered layers without the displaced source monolith', () => {
    const catalog = loadGameContent(gameContentFiles)
    expect(catalog.cultureIds).toEqual(['seyric-horizon', 'myratic-tradition'])
    expect(catalog.puzzleIds).toEqual(
      catalog.cultureIds.flatMap((culture) => catalog.puzzlesInCulture(culture)),
    )
    expect(catalog.puzzle(puzzleId('single-mark-return'))).toEqual({
      id: 'single-mark-return', diagram: expect.any(Object),
    })
    expect('source' in catalog).toBe(false)
  })

  it('keeps overlays out of exact semantic fingerprints', () => {
    const original = loadGameContent(gameContentFiles)
    const files = structuredClone(gameContentFiles) as Record<string, unknown>
    const data = files['catalog/cursebreaker.json'] as {
      cultures: unknown[]
      artifacts: Array<{ puzzle: string; name: { professional: string }; provenance: unknown }>
    }
    data.artifacts[0]!.name.professional = 'Revised museum label'
    const changed = loadGameContent(files)
    expect(changed.puzzleFingerprint(puzzleId('single-mark-return')))
      .toBe(original.puzzleFingerprint(puzzleId('single-mark-return')))
  })

  it('derives the Seyric path required to unlock Myratic solely from progression edges', () => {
    const catalog = loadGameContent(gameContentFiles)
    const seyric = new Set(catalog.puzzlesInCulture('seyric-horizon' as never))
    expect([...requiredPuzzles(catalog)].filter((id) => seyric.has(id)).sort()).toEqual([
      puzzleId('two-veils'),
      puzzleId('forked-veil'),
      puzzleId('echoed-veil'),
      puzzleId('single-mark-return'),
    ].sort())
    expect(requiredPuzzles(catalog).has(puzzleId('four-veils'))).toBe(false)
  })

  it('owns immutable snapshots and rejects unknown identities', () => {
    const catalog = loadGameContent(gameContentFiles)
    expect(() => (catalog.puzzleIds as unknown as string[]).push('intruder')).toThrow()
    expect(() => catalog.puzzle(puzzleId('missing'))).toThrow(/unknown puzzle/)
  })
})
