import { defineConfig } from 'vitest/config'
import { suiteTestConfig, testSuite } from './vitest.suites'

export default defineConfig({
  test: suiteTestConfig(testSuite()),
})
