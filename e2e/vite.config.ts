import { resolve } from 'node:path'
import { defineConfig } from 'vite'

export default defineConfig({
  root: 'app',
  build: {
    rollupOptions: {
      input: {
        app: resolve(process.cwd(), 'app/index.html'),
        relationWorkspace: resolve(process.cwd(), 'app/test/relation-workspace.html'),
      },
    },
  },
})
