import type { InlineConfig } from 'vitest/node'

export type TestSuite = 'ordinary' | 'physics' | 'all'

export function testSuite(value = process.env.VPA_TEST_SUITE): TestSuite {
  if (value === undefined || value === '') return 'ordinary'
  if (value === 'ordinary' || value === 'physics' || value === 'all') return value
  throw new Error(`unknown VPA_TEST_SUITE '${value}'; expected ordinary, physics, or all`)
}

export function suiteTestConfig(
  suite: TestSuite,
): Pick<InlineConfig, 'include' | 'exclude' | 'testTimeout' | 'hookTimeout'> {
  if (suite === 'ordinary') {
    return {
      include: ['tests/**/*.test.ts'],
      exclude: ['tests/physics/**/*.test.ts'],
      testTimeout: 5_000,
      hookTimeout: 10_000,
    }
  }
  if (suite === 'physics') {
    return {
      include: ['tests/physics/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    }
  }
  return {
    include: ['tests/**/*.test.ts'],
    exclude: [],
    testTimeout: 1_800_000,
    hookTimeout: 1_800_000,
  }
}
