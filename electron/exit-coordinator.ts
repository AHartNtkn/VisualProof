interface PreventableEvent {
  preventDefault(): void
}

interface EventSource {
  on(event: string, listener: (event: PreventableEvent) => void): unknown
}

export interface ExitCoordinator {
  confirmSavedExit(): void
  isExitConfirmed(): boolean
}

export interface ExitCoordinatorOptions {
  app: EventSource
  window: EventSource
  sendExitRequested(): void
  timeoutMs: number
  onTimeout(error: Error): void
}

export function installExitCoordinator(options: ExitCoordinatorOptions): ExitCoordinator {
  let exitRequested = false
  let exitConfirmed = false
  let failureTimer: ReturnType<typeof setTimeout> | undefined

  const handleNativeExit = (event: PreventableEvent): void => {
    if (exitConfirmed) return
    event.preventDefault()
    if (exitRequested) return
    exitRequested = true
    options.sendExitRequested()
    failureTimer = setTimeout(() => {
      options.onTimeout(new Error('Renderer did not confirm a persisted save before the exit deadline'))
    }, options.timeoutMs)
  }

  options.window.on('close', handleNativeExit)
  options.app.on('before-quit', handleNativeExit)

  return {
    confirmSavedExit(): void {
      exitConfirmed = true
      if (failureTimer !== undefined) clearTimeout(failureTimer)
    },
    isExitConfirmed(): boolean {
      return exitConfirmed
    },
  }
}
