import { serializeSaveDocument } from './save-store.js'

export const EXIT_REQUESTED_CHANNEL = 'cursebreaker:exit-requested'

interface IpcEvent {
  sender: unknown
  senderFrame: unknown
}

interface IpcMainLike {
  handle(channel: string, handler: (event: IpcEvent, ...arguments_: unknown[]) => unknown): void
}

interface WindowLike {
  webContents: { mainFrame: { url: string } }
  setFullScreen(fullscreen: boolean): void
  isFullScreen(): boolean
}

interface StoreLike {
  loadSave(): Promise<unknown | null>
  writeSave(document: unknown): Promise<void>
  replaceInvalidSave(document: unknown): Promise<void>
}

interface ExitCoordinatorLike {
  confirmSavedExit(): void
}

interface StartupCoordinatorLike {
  rendererReady(): void
  rendererFailed(message: string): void
}

export interface PlatformIpcOptions {
  ipcMain: IpcMainLike
  window: WindowLike
  store: StoreLike
  exitCoordinator: ExitCoordinatorLike
  startupCoordinator: StartupCoordinatorLike
  rendererUrl: string
  maxSaveBytes: number
  quit(): void
}

function assertTrustedSender(event: IpcEvent, options: PlatformIpcOptions): void {
  const mainFrame = options.window.webContents.mainFrame
  if (
    event.sender !== options.window.webContents
    || event.senderFrame !== mainFrame
    || mainFrame.url !== options.rendererUrl
  ) {
    throw new Error('Rejected untrusted IPC sender')
  }
}

function validateDocument(document: unknown, maxSaveBytes: number): void {
  serializeSaveDocument(document, maxSaveBytes)
}

function assertArgumentCount(channel: string, arguments_: readonly unknown[], expected: number): void {
  if (arguments_.length !== expected) {
    throw new TypeError(`${channel} expected ${expected} argument${expected === 1 ? '' : 's'}`)
  }
}

function readStartupFailureMessage(value: unknown): string {
  if (typeof value !== 'string' || value.trim().length === 0 || value.length > 4_096) {
    throw new TypeError('Startup failure message must be a nonempty string of at most 4096 characters')
  }
  return value
}

export function registerPlatformIpc(options: PlatformIpcOptions): void {
  options.ipcMain.handle('cursebreaker:load-save', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('loadSave', arguments_, 0)
    return options.store.loadSave()
  })

  options.ipcMain.handle('cursebreaker:write-save', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('writeSave', arguments_, 1)
    const document = arguments_[0]
    validateDocument(document, options.maxSaveBytes)
    await options.store.writeSave(document)
  })

  options.ipcMain.handle('cursebreaker:replace-invalid-save', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('replaceInvalidSave', arguments_, 1)
    const document = arguments_[0]
    validateDocument(document, options.maxSaveBytes)
    await options.store.replaceInvalidSave(document)
  })

  options.ipcMain.handle('cursebreaker:renderer-ready', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('rendererReady', arguments_, 0)
    options.startupCoordinator.rendererReady()
  })

  options.ipcMain.handle('cursebreaker:startup-failed', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('reportStartupFailure', arguments_, 1)
    options.startupCoordinator.rendererFailed(readStartupFailureMessage(arguments_[0]))
  })

  options.ipcMain.handle('cursebreaker:set-fullscreen', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('setFullscreen', arguments_, 1)
    const fullscreen = arguments_[0]
    if (typeof fullscreen !== 'boolean') throw new TypeError('Fullscreen must be a boolean')
    options.window.setFullScreen(fullscreen)
    return options.window.isFullScreen()
  })

  options.ipcMain.handle('cursebreaker:request-exit', async (event, ...arguments_) => {
    assertTrustedSender(event, options)
    assertArgumentCount('requestExit', arguments_, 1)
    const document = arguments_[0]
    validateDocument(document, options.maxSaveBytes)
    await options.store.writeSave(document)
    options.exitCoordinator.confirmSavedExit()
    options.quit()
  })
}
