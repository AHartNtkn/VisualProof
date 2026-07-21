import { existsSync, readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'

const source = (path: string): string => readFileSync(resolve(process.cwd(), path), 'utf8')

describe('game proof hot-path dependencies', () => {
  it('keeps codecs out of live session application', () => {
    expect(source('src/game/session.ts')).not.toMatch(/kernel\/proof\/json/)
  })

  it('keeps graph canonicalization out of blank recognition', () => {
    expect(source('src/game/blank.ts')).not.toMatch(/canonical\/explore|exploreForm/)
  })

  it('keeps codecs out of proof-context registration', () => {
    expect(source('src/kernel/proof/context.ts')).not.toMatch(/proof\/json|from '\.\/json'/)
  })

  it('does not decode a save document during encoding', () => {
    expect(source('src/game/save.ts')).not.toMatch(/decodeGameSave\(catalog, document\)/)
  })

  it('does not canonicalize every intermediate content-validation state', () => {
    expect(source('scripts/validate-game-content.ts')).not.toMatch(
      /migrationStateDigest|migrationStates|MIGRATED_VALIDATION_BASELINE/,
    )
  })

  it('contains no completed-proof theorem or archive authority', () => {
    expect(existsSync(resolve(process.cwd(), 'src/game/artifact-theorem.ts'))).toBe(false)
    expect(source('src/game/controller-state.ts')).not.toMatch(/ArtifactArchive|CompletedArtifact/)
    expect(source('src/game/save.ts')).not.toMatch(/completedArtifacts|restoreArtifact|backActions/)
  })
})
