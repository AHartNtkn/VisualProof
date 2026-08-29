import { invoke } from '@tauri-apps/api/core'

type QuitEnvironment = {
  readonly native: boolean
  readonly invoke: (command: string) => Promise<unknown>
  readonly close: () => void
  readonly closed: () => boolean
}

export function createQuitApplication(environment: QuitEnvironment): () => Promise<void> {
  return async () => {
    if (environment.native) {
      await environment.invoke('quit_game')
      return
    }
    environment.close()
    await Promise.resolve()
    if (!environment.closed()) throw new Error('Close this browser tab to quit the game.')
  }
}

export const quitApplication = createQuitApplication({
  native: (import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri') === 'tauri',
  invoke,
  close: () => window.close(),
  closed: () => window.closed,
})
