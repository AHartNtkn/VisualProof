import { defineConfig } from 'vitest/config'
import { physicsBattery } from './vitest.physics'

export default defineConfig({
  test: {
    include: [...physicsBattery],
    testTimeout: 1_800_000,
    hookTimeout: 1_800_000,
  },
})
