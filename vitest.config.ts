import { defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
    // The view relaxation tests SETTLE physics fixtures to rest — hundreds of
    // strict-descent ticks, each a full memoryless-elastica gate — so a single
    // framed-fixture settle runs for minutes, far past vitest's 5 s default.
    testTimeout: 1_800_000,
    hookTimeout: 1_800_000,
  },
})
