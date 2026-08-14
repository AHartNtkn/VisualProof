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

  it('selects the physics directory minus the wall-clock timing file, in parallel', () => {
    expect(suiteTestConfig('physics')).toEqual({
      include: ['tests/physics/**/*.test.ts'],
      exclude: ['tests/physics/frame-budget.test.ts'],
      // USER ruling 2026-07-24: a physics test settles and asserts within 30 s
      // or it fails — waiting longer can only hide a defect.
      testTimeout: 30_000,
      hookTimeout: 60_000,
    })
  })

  it('isolates the wall-clock timing tests so they measure the frame loop, not contention', () => {
    expect(suiteTestConfig('physics-timing')).toEqual({
      include: ['tests/physics/frame-budget.test.ts'],
      exclude: [],
      testTimeout: 30_000,
      hookTimeout: 60_000,
      fileParallelism: false,
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
