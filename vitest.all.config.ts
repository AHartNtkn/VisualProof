import { defineConfig } from 'vitest/config'
import { suiteTestConfig } from './vitest.suites'

export default defineConfig({
  test: suiteTestConfig('all'),
})
