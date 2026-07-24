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
      // USER ruling 2026-07-24: a physics test settles and asserts within 30 s
      // or it fails — waiting longer can only hide a defect.
      testTimeout: 30_000,
      hookTimeout: 60_000,
    })
  })

  it('selects both authorities for full validation', () => {
    expect(suiteTestConfig('all')).toEqual({
      include: ['tests/**/*.test.ts'],
      exclude: [],
      testTimeout: 30_000,
      hookTimeout: 60_000,
    })
  })
})
