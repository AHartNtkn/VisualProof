import { defineConfig } from 'vite'

export default defineConfig({
  server: {
    watch: {
      // The running game intentionally persists developer-authored content here.
      // Keep those writes in the current session; builds still import their starting bytes.
      ignored: [
        '**/content/orders.json',
        '**/content/tutorial.json',
        '**/content/tools.json',
      ],
    },
  },
})
