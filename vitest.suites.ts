import type { InlineConfig } from 'vitest/node'

export type TestSuite = 'ordinary' | 'physics' | 'physics-timing' | 'all'

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
      exclude: ['tests/physics/frame-budget.test.ts'],
      // A physics test either reaches its proven fixed point and asserts within
      // 30 s or it FAILS (USER ruling 2026-07-24): past that, waiting longer can
      // only hide a defect — a layout that doesn't rest, or a per-frame cost
      // that is itself unacceptable. Never raise this to accommodate a slow
      // test; make the test (or the physics) fast.
      testTimeout: 30_000,
      hookTimeout: 60_000,
      // Files run in parallel: nothing in this suite asserts wall-clock
      // performance. The in-test performance.now budgets are failure CAPS with
      // several-fold headroom over measured runtimes, not measurements. The
      // one file that measures wall time per frame lives in 'physics-timing'.
    }
  }
  if (suite === 'physics-timing') {
    return {
      include: ['tests/physics/frame-budget.test.ts'],
      exclude: [],
      testTimeout: 30_000,
      hookTimeout: 60_000,
      // These tests assert wall-clock frame budgets; running anything else in
      // parallel would make them measure CPU contention instead of the frame
      // loop. Isolated measurement — one file, no parallel workers.
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
