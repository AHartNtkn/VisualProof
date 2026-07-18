import { readFile } from 'node:fs/promises'
import ts from 'typescript'
import { describe, expect, test, vi } from 'vitest'

async function compilePreload(): Promise<string> {
  const source = await readFile('electron/preload.cts', 'utf8')
  return ts.transpileModule(source, {
    compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 },
  }).outputText
}

async function executeCompiledPreload() {
  const compiled = await compilePreload()
  const exposed: Array<[string, Record<string, (...arguments_: any[]) => unknown>]> = []
  const transport = { invoke: vi.fn(), on: vi.fn(), removeListener: vi.fn() }
  const sandboxRequire = vi.fn((moduleName: string) => {
    if (moduleName !== 'electron') throw new Error(`Sandbox preload required unsupported module ${moduleName}`)
    return {
      contextBridge: { exposeInMainWorld: (name: string, api: Record<string, (...arguments_: any[]) => unknown>) => exposed.push([name, api]) },
      ipcRenderer: transport,
    }
  })
  Function('require', 'exports', 'module', compiled)(sandboxRequire, {}, { exports: {} })
  return { compiled, exposed, sandboxRequire, transport }
}

describe('isolated preload API', () => {
  test('the compiled sandbox preload is self-contained and exposes rejected-save replacement narrowly', async () => {
    const { compiled, exposed, sandboxRequire } = await executeCompiledPreload()
    const api = exposed[0]?.[1]

    expect(compiled).not.toMatch(/require\(["']\.\.?\//)
    expect(sandboxRequire.mock.calls).toEqual([['electron']])
    expect(exposed[0]?.[0]).toBe('cursebreakerPlatform')
    expect(Object.keys(api ?? {}).sort()).toEqual([
      'loadSave',
      'onExitRequested',
      'rendererReady',
      'replaceInvalidSave',
      'reportStartupFailure',
      'requestExit',
      'setFullscreen',
      'writeSave',
    ])
    expect(api).not.toHaveProperty('invoke')
    expect(api).not.toHaveProperty('send')
    expect(api).not.toHaveProperty('ipcRenderer')
  })

  test('maps calls to fixed internal channels and returns an unsubscribe function', async () => {
    const { exposed, transport } = await executeCompiledPreload()
    const api = exposed[0]?.[1]
    expect(api).toBeDefined()
    const callback = vi.fn()

    await api?.loadSave?.()
    await api?.writeSave?.({ revision: 1 })
    await api?.replaceInvalidSave?.({ revision: 4 })
    await api?.rendererReady?.()
    await api?.reportStartupFailure?.('fixture bootstrap exploded')
    await api?.setFullscreen?.(false)
    await api?.requestExit?.({ revision: 2 })
    const unsubscribe = api?.onExitRequested?.(callback) as (() => void) | undefined
    const listener = transport.on.mock.calls[0]?.[1]
    listener?.({ sender: 'hidden' })
    unsubscribe?.()

    expect(transport.invoke.mock.calls).toEqual([
      ['cursebreaker:load-save'],
      ['cursebreaker:write-save', { revision: 1 }],
      ['cursebreaker:replace-invalid-save', { revision: 4 }],
      ['cursebreaker:renderer-ready'],
      ['cursebreaker:startup-failed', 'fixture bootstrap exploded'],
      ['cursebreaker:set-fullscreen', false],
      ['cursebreaker:request-exit', { revision: 2 }],
    ])
    expect(callback).toHaveBeenCalledOnce()
    expect(transport.removeListener).toHaveBeenCalledWith('cursebreaker:exit-requested', listener)
  })
})
