import { app, BrowserWindow, ipcMain } from 'electron'
import path from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import { installExitCoordinator } from './exit-coordinator.js'
import { EXIT_REQUESTED_CHANNEL, registerPlatformIpc } from './ipc-boundary.js'
import { DEFAULT_MAX_SAVE_BYTES, SaveStore } from './save-store.js'
import { installStartupCoordinator } from './startup-coordinator.js'
import { initialFullscreenFromSave, installWindowSecurity, secureWindowOptions } from './window-policy.js'

const currentDirectory = path.dirname(fileURLToPath(import.meta.url))
const rendererPath = path.resolve(currentDirectory, '../app/dist/index.html')
const rendererUrl = pathToFileURL(rendererPath).href
const preloadPath = path.join(currentDirectory, 'preload.cjs')

async function createMainWindow(): Promise<void> {
  const saveStore = new SaveStore({
    directory: path.join(app.getPath('userData'), 'cursebreaker-save'),
    maxBytes: DEFAULT_MAX_SAVE_BYTES,
  })
  const savedDocument = await saveStore.loadSave()
  const mainWindow = new BrowserWindow(
    secureWindowOptions(preloadPath, initialFullscreenFromSave(savedDocument)),
  )
  installWindowSecurity(mainWindow.webContents, rendererUrl)
  const startupCoordinator = installStartupCoordinator({
    window: mainWindow,
    timeoutMs: 15_000,
    onFailure: (error) => {
      console.error('Failed to start Cursebreaker', error)
      app.exit(1)
    },
  })
  const exitCoordinator = installExitCoordinator({
    app,
    window: mainWindow,
    sendExitRequested: () => mainWindow.webContents.send(EXIT_REQUESTED_CHANNEL),
    timeoutMs: 15_000,
    onTimeout: (error) => console.error(error),
  })
  registerPlatformIpc({
    ipcMain,
    window: mainWindow,
    store: saveStore,
    exitCoordinator,
    startupCoordinator,
    rendererUrl,
    maxSaveBytes: DEFAULT_MAX_SAVE_BYTES,
    quit: () => app.quit(),
  })
  await mainWindow.loadFile(rendererPath)
}

app.whenReady()
  .then(createMainWindow)
  .catch((error: unknown) => {
    console.error('Failed to start Cursebreaker', error)
    app.exit(1)
  })

app.on('window-all-closed', () => {
  if (process.platform !== 'darwin') app.quit()
})
