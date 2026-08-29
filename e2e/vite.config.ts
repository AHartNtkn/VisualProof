import { resolve } from 'node:path'
import { defineConfig } from 'vite'

export default defineConfig({
  root: 'app',
  build: {
    rollupOptions: {
      input: {
        app: resolve(process.cwd(), 'app/index.html'),
        view3Render: resolve(process.cwd(), 'app/test/view3-render.html'),
      },
    },
  },
})
