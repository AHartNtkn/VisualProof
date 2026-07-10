import { defineConfig } from '@playwright/test'

export default defineConfig({
  testDir: 'e2e',
  use: { baseURL: 'http://localhost:4173' },
  webServer: [
    {
      command: 'npx vite build app --logLevel error && npx vite preview app --port 4173 --strictPort',
      url: 'http://localhost:4173',
      reuseExistingServer: false,
      timeout: 60000,
    },
    {
      command: 'npx vite --host 127.0.0.1 --port 4174 --strictPort',
      url: 'http://127.0.0.1:4174/ui-lab/round13-a.html',
      reuseExistingServer: false,
      timeout: 60000,
    },
  ],
  projects: [{ name: 'chromium', use: { browserName: 'chromium' } }],
})
