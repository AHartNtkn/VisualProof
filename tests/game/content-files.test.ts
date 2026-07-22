import { describe, expect, it } from 'vitest'
import { gameContentFiles } from '../../src/game/content/files'

type RuntimeManifest = {
  readonly puzzles: readonly string[]
  readonly definitions: readonly string[]
  readonly progression: string
  readonly catalog: string
  readonly guidance: string
}

describe('data-driven runtime content inventory', () => {
  it('makes every manifest-owned runtime file available automatically', () => {
    const manifest = gameContentFiles['manifest.json'] as RuntimeManifest
    const selected = [
      ...manifest.puzzles,
      ...manifest.definitions,
      manifest.progression,
      manifest.catalog,
      manifest.guidance,
    ]
    expect(selected.filter((path) => !Object.hasOwn(gameContentFiles, path))).toEqual([])
  })

  it('keeps build-only records out of the runtime inventory', () => {
    expect(Object.keys(gameContentFiles).filter((path) =>
      /^(?:coverage|validation|schemas)\//.test(path),
    )).toEqual([])
  })
})
