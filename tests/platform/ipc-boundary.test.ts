import { describe, expect, test, vi } from 'vitest'

async function loadIpcBoundaryModule(): Promise<any> {
  const modulePath = '../../electron/ipc-boundary'
  return import(modulePath).catch(() => null)
}

function createHarness() {
  const handlers = new Map<string, (...args: any[]) => unknown>()
  const mainFrame = { url: 'file:///game/app/dist/index.html' }
  const webContents = { mainFrame, setFullScreen: vi.fn() }
  const window = {
    webContents,
    setFullScreen: vi.fn(),
    isFullScreen: vi.fn(() => true),
  }
  const store = { loadSave: vi.fn(async () => null), writeSave: vi.fn(async () => undefined) }
  const exitCoordinator = { confirmSavedExit: vi.fn() }
  const quit = vi.fn()
  const ipcMain = { handle: vi.fn((channel, handler) => handlers.set(channel, handler)) }
  return { handlers, ipcMain, mainFrame, webContents, window, store, exitCoordinator, quit }
}

describe('main-process IPC boundary', () => {
  test('rejects calls not sent by the local main renderer frame', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({
      ...harness,
      rendererUrl: harness.mainFrame.url,
      maxSaveBytes: 64,
    })
    const loadSave = harness.handlers.get('cursebreaker:load-save')

    await expect(loadSave?.({ sender: harness.webContents, senderFrame: { url: harness.mainFrame.url } })).rejects.toThrow(/sender/i)
    await expect(loadSave?.({ sender: harness.webContents, senderFrame: harness.mainFrame })).resolves.toBeNull()
  })

  test('rejects invalid or oversized arguments before persistence', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 32 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }

    await expect(harness.handlers.get('cursebreaker:write-save')?.(event, { fn: () => undefined })).rejects.toThrow()
    await expect(harness.handlers.get('cursebreaker:write-save')?.(event, { text: 'x'.repeat(100) })).rejects.toThrow(/size/i)
    await expect(harness.handlers.get('cursebreaker:set-fullscreen')?.(event, 'false')).rejects.toThrow(/boolean/i)
    expect(harness.store.writeSave).not.toHaveBeenCalled()
  })

  test('returns authoritative fullscreen state', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 64 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }

    await expect(harness.handlers.get('cursebreaker:set-fullscreen')?.(event, false)).resolves.toBe(true)
    expect(harness.window.setFullScreen).toHaveBeenCalledWith(false)
    expect(harness.window.isFullScreen).toHaveBeenCalledOnce()
  })

  test('persists the supplied save before confirming and quitting', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    const order: string[] = []
    harness.store.writeSave.mockImplementation(async () => { order.push('save') })
    harness.exitCoordinator.confirmSavedExit.mockImplementation(() => { order.push('confirm') })
    harness.quit.mockImplementation(() => { order.push('quit') })
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 64 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }

    await harness.handlers.get('cursebreaker:request-exit')?.(event, { revision: 9 })

    expect(order).toEqual(['save', 'confirm', 'quit'])
  })
})
