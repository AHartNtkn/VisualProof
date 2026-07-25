import type { InlineConfig } from 'vitest/node'

export type TestSuite = 'ordinary' | 'physics' | 'all'

export function suiteTestConfig(
  suite: TestSuite,
): Pick<InlineConfig, 'include' | 'exclude' | 'testTimeout' | 'hookTimeout' | 'fileParallelism'> {
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
      // A physics test either reaches its proven fixed point and asserts within
      // 30 s or it FAILS (USER ruling 2026-07-24): past that, waiting longer can
      // only hide a defect — a layout that doesn't rest, or a per-frame cost
      // that is itself unacceptable. Never raise this to accommodate a slow
      // test; make the test (or the physics) fast.
      testTimeout: 30_000,
      hookTimeout: 60_000,
      // Physics tests assert WALL-CLOCK settle budgets; running files in
      // parallel workers makes those budgets measure CPU contention instead
      // of the solver (natBody: 16.4 s isolated vs 20 s+ under suite load).
      // Wall budgets require isolated measurement — one file at a time.
      fileParallelism: false,
    }
  }
  return {
    include: ['tests/**/*.test.ts'],
    exclude: [],
    testTimeout: 30_000,
    hookTimeout: 60_000,
  }
}
