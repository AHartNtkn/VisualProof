import { readFile } from 'node:fs/promises'
import path from 'node:path'
import { describe, expect, test, vi } from 'vitest'

async function loadWindowPolicyModule(): Promise<any> {
  const modulePath = '../../electron/window-policy'
  return import(modulePath).catch(() => null)
}

describe('Electron window policy', () => {
  test.each([
    [null, true],
    [{}, true],
    [{ settings: {} }, true],
    [{ settings: { fullscreen: 'false' } }, true],
    [{ settings: { fullscreen: false } }, false],
    [{ settings: { fullscreen: true } }, true],
  ])('defaults fullscreen safely for saved document %#', async (savedDocument, expected) => {
    const module = await loadWindowPolicyModule()
    expect(module).not.toBeNull()
    expect(module.initialFullscreenFromSave(savedDocument)).toBe(expected)
  })

  test('constructs a borderless isolated sandboxed renderer with no Node authority', async () => {
    const module = await loadWindowPolicyModule()
    expect(module).not.toBeNull()

    expect(module.secureWindowOptions('/absolute/preload.cjs', false)).toMatchObject({
      frame: false,
      fullscreen: false,
      show: false,
      webPreferences: {
        preload: '/absolute/preload.cjs',
        nodeIntegration: false,
        contextIsolation: true,
        sandbox: true,
        experimentalFeatures: false,
      },
    })
  })

  test('denies renderer-created windows and unexpected navigation', async () => {
    const module = await loadWindowPolicyModule()
    expect(module).not.toBeNull()
    let openHandler: ((details: { url: string }) => { action: string }) | undefined
    let navigationHandler: ((event: { preventDefault: () => void }, url: string) => void) | undefined
    const webContents = {
      setWindowOpenHandler: vi.fn((handler) => { openHandler = handler }),
      on: vi.fn((event, handler) => { if (event === 'will-navigate') navigationHandler = handler }),
    }
    module.installWindowSecurity(webContents, 'file:///game/app/dist/index.html')

    expect(openHandler?.({ url: 'https://example.com' })).toEqual({ action: 'deny' })
    const allowedEvent = { preventDefault: vi.fn() }
    navigationHandler?.(allowedEvent, 'file:///game/app/dist/index.html')
    expect(allowedEvent.preventDefault).not.toHaveBeenCalled()
    const deniedEvent = { preventDefault: vi.fn() }
    navigationHandler?.(deniedEvent, 'file:///tmp/untrusted.html')
    expect(deniedEvent.preventDefault).toHaveBeenCalledOnce()
  })

  test('the packaged renderer document has a restrictive local-only CSP', async () => {
    const html = await readFile(path.resolve('app/index.html'), 'utf8')
    expect(html).toMatch(/Content-Security-Policy/)
    expect(html).toContain("default-src 'self'")
    expect(html).toContain("connect-src 'none'")
    expect(html).toContain("object-src 'none'")
    expect(html).not.toMatch(/unsafe-eval|https?:/)
  })
})
