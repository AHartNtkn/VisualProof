import { describe, expect, it } from 'vitest'
import {
  artifactRuntimeCatalog,
  editorRuntimeCatalog,
  longRuntimeCatalog,
  motionRuntimeCatalog,
} from './runtime-catalog-fixture'

describe('authoritative runtime decisive catalogs', () => {
  it('builds verified artifact and long-scroll catalogs through production validation', () => {
    expect(artifactRuntimeCatalog().puzzleIds).toHaveLength(3)
    expect(editorRuntimeCatalog().puzzleIds).toHaveLength(1)
    expect(longRuntimeCatalog().puzzleIds).toHaveLength(16)
    expect(motionRuntimeCatalog().puzzleIds).toHaveLength(1)
  })
})
