import { configDefaults, defineConfig } from 'vitest/config'
import { physicsBattery } from './vitest.physics'

export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
    exclude: [...configDefaults.exclude, ...physicsBattery],
    // Some ordinary view tests settle a fixture before checking rendering or
    // interaction behavior, so they still need more than Vitest's 5 s default.
    // The dedicated multi-minute physics batteries are excluded above.
    testTimeout: 1_800_000,
    hookTimeout: 1_800_000,
  },
})
