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
}

interface ExitCoordinatorLike {
  confirmSavedExit(): void
}

export interface PlatformIpcOptions {
  ipcMain: IpcMainLike
  window: WindowLike
  store: StoreLike
  exitCoordinator: ExitCoordinatorLike
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

export function registerPlatformIpc(options: PlatformIpcOptions): void {
  options.ipcMain.handle('cursebreaker:load-save', async (event) => {
    assertTrustedSender(event, options)
    return options.store.loadSave()
  })

  options.ipcMain.handle('cursebreaker:write-save', async (event, document) => {
    assertTrustedSender(event, options)
    validateDocument(document, options.maxSaveBytes)
    await options.store.writeSave(document)
  })

  options.ipcMain.handle('cursebreaker:set-fullscreen', async (event, fullscreen) => {
    assertTrustedSender(event, options)
    if (typeof fullscreen !== 'boolean') throw new TypeError('Fullscreen must be a boolean')
    options.window.setFullScreen(fullscreen)
    return options.window.isFullScreen()
  })

  options.ipcMain.handle('cursebreaker:request-exit', async (event, document) => {
    assertTrustedSender(event, options)
    validateDocument(document, options.maxSaveBytes)
    await options.store.writeSave(document)
    options.exitCoordinator.confirmSavedExit()
    options.quit()
  })
}
