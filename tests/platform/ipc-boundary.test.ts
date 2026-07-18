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
  const store = {
    loadSave: vi.fn(async () => null),
    writeSave: vi.fn(async () => undefined),
    replaceInvalidSave: vi.fn(async () => undefined),
  }
  const exitCoordinator = { confirmSavedExit: vi.fn() }
  const startupCoordinator = { rendererReady: vi.fn(), rendererFailed: vi.fn() }
  const quit = vi.fn()
  const ipcMain = { handle: vi.fn((channel, handler) => handlers.set(channel, handler)) }
  return { handlers, ipcMain, mainFrame, webContents, window, store, exitCoordinator, startupCoordinator, quit }
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
    await expect(harness.handlers.get('cursebreaker:replace-invalid-save')?.(event, { text: 'x'.repeat(100) })).rejects.toThrow(/size/i)
    await expect(harness.handlers.get('cursebreaker:set-fullscreen')?.(event, 'false')).rejects.toThrow(/boolean/i)
    expect(harness.store.writeSave).not.toHaveBeenCalled()
    expect(harness.store.replaceInvalidSave).not.toHaveBeenCalled()
  })

  test('rejects missing and trailing arguments on every invoke channel', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 64 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }

    await expect(harness.handlers.get('cursebreaker:load-save')?.(event, 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:write-save')?.(event)).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:write-save')?.(event, { revision: 1 }, 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:replace-invalid-save')?.(event)).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:replace-invalid-save')?.(event, { revision: 4 }, 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:renderer-ready')?.(event, 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:startup-failed')?.(event)).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:startup-failed')?.(event, '')).rejects.toThrow(/message/i)
    await expect(harness.handlers.get('cursebreaker:startup-failed')?.(event, 'x', 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:set-fullscreen')?.(event)).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:set-fullscreen')?.(event, true, 'trailing')).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:request-exit')?.(event)).rejects.toThrow(/argument/i)
    await expect(harness.handlers.get('cursebreaker:request-exit')?.(event, { revision: 1 }, 'trailing')).rejects.toThrow(/argument/i)
    expect(harness.store.loadSave).not.toHaveBeenCalled()
    expect(harness.store.writeSave).not.toHaveBeenCalled()
    expect(harness.store.replaceInvalidSave).not.toHaveBeenCalled()
    expect(harness.window.setFullScreen).not.toHaveBeenCalled()
    expect(harness.startupCoordinator.rendererReady).not.toHaveBeenCalled()
    expect(harness.startupCoordinator.rendererFailed).not.toHaveBeenCalled()
    expect(harness.quit).not.toHaveBeenCalled()
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

  test('validates and atomically replaces a renderer-rejected save', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 64 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }
    const replacement = { revision: 4 }

    await harness.handlers.get('cursebreaker:replace-invalid-save')?.(event, replacement)

    expect(harness.store.replaceInvalidSave).toHaveBeenCalledWith(replacement)
    expect(harness.store.writeSave).not.toHaveBeenCalled()
  })

  test('accepts only trusted readiness and bounded fatal-startup reports', async () => {
    const module = await loadIpcBoundaryModule()
    expect(module).not.toBeNull()
    const harness = createHarness()
    module.registerPlatformIpc({ ...harness, rendererUrl: harness.mainFrame.url, maxSaveBytes: 64 })
    const event = { sender: harness.webContents, senderFrame: harness.mainFrame }

    await harness.handlers.get('cursebreaker:renderer-ready')?.(event)
    await harness.handlers.get('cursebreaker:startup-failed')?.(event, 'fixture bootstrap exploded')

    expect(harness.startupCoordinator.rendererReady).toHaveBeenCalledOnce()
    expect(harness.startupCoordinator.rendererFailed).toHaveBeenCalledWith('fixture bootstrap exploded')
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
