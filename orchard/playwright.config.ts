import { defineConfig } from '@playwright/test'

export default defineConfig({
  testDir: 'e2e',
  testIgnore: process.env['ORCHARD_STRESS'] === '1' ? [] : ['**/orchard-stress.spec.ts'],
  use: { baseURL: 'http://127.0.0.1:4174' },
  webServer: {
    command: 'npx vite . --host 127.0.0.1 --port 4174 --strictPort',
    url: 'http://127.0.0.1:4174',
    reuseExistingServer: false,
    timeout: 60_000,
  },
  projects: [{ name: 'chromium', use: { browserName: 'chromium' } }],
})
