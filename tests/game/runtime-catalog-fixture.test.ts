import { describe, expect, it } from 'vitest'
import {
  artifactRuntimeCatalog,
  editorRuntimeCatalog,
  longRuntimeCatalog,
  motionRuntimeCatalog,
} from './runtime-catalog-fixture'

describe('authoritative runtime decisive catalogs', () => {
  it('builds verified artifact and long-scroll catalogs through production validation', () => {
    expect(artifactRuntimeCatalog().source.puzzles).toHaveLength(3)
    expect(editorRuntimeCatalog().source.puzzles).toHaveLength(1)
    expect(longRuntimeCatalog().source.puzzles).toHaveLength(16)
    expect(motionRuntimeCatalog().source.puzzles).toHaveLength(1)
  })
})
