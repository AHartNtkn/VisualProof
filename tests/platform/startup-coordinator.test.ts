import { EventEmitter } from 'node:events'
import { describe, expect, test, vi } from 'vitest'

async function loadStartupCoordinatorModule(): Promise<any> {
  const modulePath = '../../electron/startup-coordinator'
  return import(modulePath).catch(() => null)
}

describe('desktop startup coordination', () => {
  test('reveals the hidden window exactly once only after renderer readiness', async () => {
    vi.useFakeTimers()
    const module = await loadStartupCoordinatorModule()
    expect(module).not.toBeNull()
    const webContents = new EventEmitter()
    const window = { webContents, show: vi.fn() }
    const onFailure = vi.fn()
    const coordinator = module.installStartupCoordinator({ window, timeoutMs: 100, onFailure })

    coordinator.rendererReady()
    coordinator.rendererReady()
    vi.advanceTimersByTime(100)

    expect(window.show).toHaveBeenCalledOnce()
    expect(coordinator.isReady()).toBe(true)
    expect(onFailure).not.toHaveBeenCalled()
    vi.useRealTimers()
  })

  test('terminates startup on explicit renderer failure without showing the window', async () => {
    const module = await loadStartupCoordinatorModule()
    expect(module).not.toBeNull()
    const window = { webContents: new EventEmitter(), show: vi.fn() }
    const onFailure = vi.fn()
    const coordinator = module.installStartupCoordinator({ window, timeoutMs: 100, onFailure })

    coordinator.rendererFailed('fixture bootstrap exploded')

    expect(window.show).not.toHaveBeenCalled()
    expect(onFailure).toHaveBeenCalledOnce()
    expect(onFailure.mock.calls[0]?.[0]).toMatchObject({ message: expect.stringContaining('fixture bootstrap exploded') })
  })

  test.each([
    ['preload-error', [{}, '/game/preload.cjs', new Error('preload exploded')], /preload exploded/],
    ['render-process-gone', [{}, { reason: 'crashed', exitCode: 9 }], /crashed.*9/],
    ['did-fail-load', [{}, -6, 'renderer missing', 'file:///missing', true], /renderer missing/],
  ])('terminates startup for %s before readiness', async (event, arguments_, expected) => {
    const module = await loadStartupCoordinatorModule()
    expect(module).not.toBeNull()
    const webContents = new EventEmitter()
    const window = { webContents, show: vi.fn() }
    const onFailure = vi.fn()
    module.installStartupCoordinator({ window, timeoutMs: 100, onFailure })

    webContents.emit(event, ...arguments_)

    expect(window.show).not.toHaveBeenCalled()
    expect(onFailure).toHaveBeenCalledOnce()
    expect(onFailure.mock.calls[0]?.[0].message).toMatch(expected)
  })

  test('terminates when no renderer reports readiness before the deadline', async () => {
    vi.useFakeTimers()
    const module = await loadStartupCoordinatorModule()
    expect(module).not.toBeNull()
    const window = { webContents: new EventEmitter(), show: vi.fn() }
    const onFailure = vi.fn()
    module.installStartupCoordinator({ window, timeoutMs: 100, onFailure })

    vi.advanceTimersByTime(100)

    expect(window.show).not.toHaveBeenCalled()
    expect(onFailure).toHaveBeenCalledOnce()
    expect(onFailure.mock.calls[0]?.[0].message).toMatch(/readiness.*deadline/i)
    vi.useRealTimers()
  })
})
