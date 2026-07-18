interface NavigationEvent {
  preventDefault(): void
}

interface SecuredWebContents {
  setWindowOpenHandler(handler: (details: { url: string }) => { action: 'deny' }): void
  on(event: 'will-navigate', handler: (event: NavigationEvent, url: string) => void): void
}

export function initialFullscreenFromSave(savedDocument: unknown): boolean {
  if (savedDocument === null || typeof savedDocument !== 'object' || Array.isArray(savedDocument)) return true
  const settings = (savedDocument as Record<string, unknown>).settings
  if (settings === null || typeof settings !== 'object' || Array.isArray(settings)) return true
  const fullscreen = (settings as Record<string, unknown>).fullscreen
  return typeof fullscreen === 'boolean' ? fullscreen : true
}

export function secureWindowOptions(preload: string, fullscreen: boolean) {
  return {
    frame: false,
    fullscreen,
    show: false,
    webPreferences: {
      preload,
      nodeIntegration: false,
      contextIsolation: true,
      sandbox: true,
      experimentalFeatures: false,
    },
  } as const
}

export function installWindowSecurity(webContents: SecuredWebContents, rendererUrl: string): void {
  webContents.setWindowOpenHandler(() => ({ action: 'deny' }))
  webContents.on('will-navigate', (event, url) => {
    if (url !== rendererUrl) event.preventDefault()
  })
}
