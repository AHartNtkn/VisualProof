interface PreloadTransport {
  invoke(channel: string, ...arguments_: unknown[]): Promise<unknown>
  on(channel: string, listener: (event: unknown) => void): void
  removeListener(channel: string, listener: (event: unknown) => void): void
}

function createPlatformApi(transport: PreloadTransport) {
  return Object.freeze({
    loadSave: (): Promise<unknown | null> =>
      transport.invoke('cursebreaker:load-save') as Promise<unknown | null>,
    writeSave: (document: unknown): Promise<void> =>
      transport.invoke('cursebreaker:write-save', document) as Promise<void>,
    setFullscreen: (fullscreen: boolean): Promise<boolean> =>
      transport.invoke('cursebreaker:set-fullscreen', fullscreen) as Promise<boolean>,
    requestExit: (document: unknown): Promise<void> =>
      transport.invoke('cursebreaker:request-exit', document) as Promise<void>,
    onExitRequested: (callback: () => void): (() => void) => {
      const listener = (_event: unknown): void => callback()
      transport.on('cursebreaker:exit-requested', listener)
      return () => transport.removeListener('cursebreaker:exit-requested', listener)
    },
  })
}

export = { createPlatformApi }
