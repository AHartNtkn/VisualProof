import { describe, expect, it } from 'vitest'
import { suiteTestConfig } from '../../vitest.suites'

describe('Vitest suite ownership', () => {
  it('defaults to ordinary validation', () => {
    expect(suiteTestConfig('ordinary')).toEqual({
      include: ['tests/**/*.test.ts'],
      exclude: ['tests/physics/**/*.test.ts'],
      testTimeout: 5_000,
      hookTimeout: 10_000,
    })
  })

  it('selects exactly the expensive physics directory', () => {
    expect(suiteTestConfig('physics')).toEqual({
      include: ['tests/physics/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    })
  })

  it('selects both authorities for full validation', () => {
    expect(suiteTestConfig('all')).toEqual({
      include: ['tests/**/*.test.ts'],
      exclude: [],
      testTimeout: 1_800_000,
      hookTimeout: 1_800_000,
    })
  })
})
