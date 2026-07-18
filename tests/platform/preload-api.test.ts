import { readFile } from 'node:fs/promises'
import ts from 'typescript'
import { describe, expect, test, vi } from 'vitest'

async function loadPreloadApiModule(): Promise<any> {
  const source = await readFile('electron/preload-api.cts', 'utf8')
  const compiled = ts.transpileModule(source, {
    compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 },
  }).outputText
  const commonJsModule = { exports: {} as Record<string, unknown> }
  Function('exports', 'module', compiled)(commonJsModule.exports, commonJsModule)
  return commonJsModule.exports
}

describe('isolated preload API', () => {
  test('exposes exactly five narrow capabilities and never raw IPC', async () => {
    const module = await loadPreloadApiModule()
    expect(module).not.toBeNull()
    const transport = { invoke: vi.fn(), on: vi.fn(), removeListener: vi.fn() }
    const api = module.createPlatformApi(transport)

    expect(Object.keys(api).sort()).toEqual([
      'loadSave',
      'onExitRequested',
      'requestExit',
      'setFullscreen',
      'writeSave',
    ])
    expect(api).not.toHaveProperty('invoke')
    expect(api).not.toHaveProperty('send')
    expect(api).not.toHaveProperty('ipcRenderer')
  })

  test('maps calls to fixed internal channels and returns an unsubscribe function', async () => {
    const module = await loadPreloadApiModule()
    expect(module).not.toBeNull()
    const transport = { invoke: vi.fn(), on: vi.fn(), removeListener: vi.fn() }
    const api = module.createPlatformApi(transport)
    const callback = vi.fn()

    await api.loadSave()
    await api.writeSave({ revision: 1 })
    await api.setFullscreen(false)
    await api.requestExit({ revision: 2 })
    const unsubscribe = api.onExitRequested(callback)
    const listener = transport.on.mock.calls[0]?.[1]
    listener?.({ sender: 'hidden' })
    unsubscribe()

    expect(transport.invoke.mock.calls).toEqual([
      ['cursebreaker:load-save'],
      ['cursebreaker:write-save', { revision: 1 }],
      ['cursebreaker:set-fullscreen', false],
      ['cursebreaker:request-exit', { revision: 2 }],
    ])
    expect(callback).toHaveBeenCalledOnce()
    expect(transport.removeListener).toHaveBeenCalledWith('cursebreaker:exit-requested', listener)
  })
})
