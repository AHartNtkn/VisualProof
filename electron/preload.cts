const { contextBridge, ipcRenderer } = require('electron') as typeof import('electron')

contextBridge.exposeInMainWorld('cursebreakerPlatform', Object.freeze({
  loadSave: (): Promise<unknown | null> =>
    ipcRenderer.invoke('cursebreaker:load-save') as Promise<unknown | null>,
  writeSave: (document: unknown): Promise<void> =>
    ipcRenderer.invoke('cursebreaker:write-save', document) as Promise<void>,
  replaceInvalidSave: (document: unknown): Promise<void> =>
    ipcRenderer.invoke('cursebreaker:replace-invalid-save', document) as Promise<void>,
  rendererReady: (): Promise<void> =>
    ipcRenderer.invoke('cursebreaker:renderer-ready') as Promise<void>,
  reportStartupFailure: (message: string): Promise<void> =>
    ipcRenderer.invoke('cursebreaker:startup-failed', message) as Promise<void>,
  setFullscreen: (fullscreen: boolean): Promise<boolean> =>
    ipcRenderer.invoke('cursebreaker:set-fullscreen', fullscreen) as Promise<boolean>,
  requestExit: (document: unknown): Promise<void> =>
    ipcRenderer.invoke('cursebreaker:request-exit', document) as Promise<void>,
  onExitRequested: (callback: () => void): (() => void) => {
    const listener = (): void => callback()
    ipcRenderer.on('cursebreaker:exit-requested', listener)
    return () => ipcRenderer.removeListener('cursebreaker:exit-requested', listener)
  },
}))
