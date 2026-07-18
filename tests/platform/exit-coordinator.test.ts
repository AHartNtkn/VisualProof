import { EventEmitter } from 'node:events'
import { describe, expect, test, vi } from 'vitest'

async function loadExitCoordinatorModule(): Promise<any> {
  const modulePath = '../../electron/exit-coordinator'
  return import(modulePath).catch(() => null)
}

describe('native exit coordination', () => {
  test('requests a save-bearing exit exactly once and prevents native quit until confirmation', async () => {
    vi.useFakeTimers()
    const module = await loadExitCoordinatorModule()
    expect(module).not.toBeNull()
    const app = new EventEmitter()
    const window = new EventEmitter()
    const sendExitRequested = vi.fn()
    const onTimeout = vi.fn()
    const coordinator = module.installExitCoordinator({ app, window, sendExitRequested, timeoutMs: 100, onTimeout })
    const closeEvent = { preventDefault: vi.fn() }
    const quitEvent = { preventDefault: vi.fn() }

    window.emit('close', closeEvent)
    app.emit('before-quit', quitEvent)

    expect(closeEvent.preventDefault).toHaveBeenCalledOnce()
    expect(quitEvent.preventDefault).toHaveBeenCalledOnce()
    expect(sendExitRequested).toHaveBeenCalledOnce()
    expect(coordinator.isExitConfirmed()).toBe(false)

    vi.advanceTimersByTime(100)
    expect(onTimeout).toHaveBeenCalledOnce()
    expect(coordinator.isExitConfirmed()).toBe(false)
    vi.useRealTimers()
  })

  test('allows close only after the explicit save has been confirmed', async () => {
    const module = await loadExitCoordinatorModule()
    expect(module).not.toBeNull()
    const app = new EventEmitter()
    const window = new EventEmitter()
    const coordinator = module.installExitCoordinator({
      app,
      window,
      sendExitRequested: vi.fn(),
      timeoutMs: 100,
      onTimeout: vi.fn(),
    })
    coordinator.confirmSavedExit()
    const closeEvent = { preventDefault: vi.fn() }

    window.emit('close', closeEvent)

    expect(closeEvent.preventDefault).not.toHaveBeenCalled()
    expect(coordinator.isExitConfirmed()).toBe(true)
  })
})
