import { defineConfig } from 'vite'

export default defineConfig({
  server: {
    watch: {
      // The running game intentionally persists developer-created orders here.
      // Keep that write in the current session; builds still import its starting bytes.
      ignored: ['**/game/content/orders.json'],
    },
  },
})
