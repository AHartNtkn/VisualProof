interface StartupWebContents {
  on(event: string, listener: (...arguments_: any[]) => void): unknown
}

interface StartupWindow {
  readonly webContents: StartupWebContents
  show(): void
}

export interface StartupCoordinator {
  rendererReady(): void
  rendererFailed(message: string): void
  isReady(): boolean
}

export interface StartupCoordinatorOptions {
  readonly window: StartupWindow
  readonly timeoutMs: number
  readonly onFailure: (error: Error) => void
}

const errorMessage = (error: unknown): string =>
  error instanceof Error ? error.message : String(error)

export function installStartupCoordinator(
  options: StartupCoordinatorOptions,
): StartupCoordinator {
  let ready = false
  let failed = false
  const fail = (error: Error): void => {
    if (ready || failed) return
    failed = true
    clearTimeout(deadline)
    options.onFailure(error)
  }
  const deadline = setTimeout(() => {
    fail(new Error('Renderer did not report readiness before the startup deadline'))
  }, options.timeoutMs)

  options.window.webContents.on(
    'preload-error',
    (_event, preloadPath: string, error: unknown) => {
      fail(new Error(`Preload failed at ${preloadPath}: ${errorMessage(error)}`))
    },
  )
  options.window.webContents.on(
    'render-process-gone',
    (_event, details: { reason?: unknown; exitCode?: unknown }) => {
      fail(new Error(
        `Renderer process ${String(details?.reason ?? 'failed')} with exit code ${String(details?.exitCode ?? 'unknown')}`,
      ))
    },
  )
  options.window.webContents.on(
    'did-fail-load',
    (
      _event,
      errorCode: number,
      errorDescription: string,
      validatedUrl: string,
      isMainFrame: boolean,
    ) => {
      if (isMainFrame === false) return
      fail(new Error(
        `Renderer failed to load ${validatedUrl}: ${errorDescription} (${errorCode})`,
      ))
    },
  )

  return {
    rendererReady(): void {
      if (ready || failed) return
      ready = true
      clearTimeout(deadline)
      options.window.show()
    },
    rendererFailed(message: string): void {
      fail(new Error(`Renderer startup failed: ${message}`))
    },
    isReady(): boolean {
      return ready
    },
  }
}
