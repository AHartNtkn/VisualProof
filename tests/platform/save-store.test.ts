import { mkdtemp, readFile, readdir, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterEach, describe, expect, test } from 'vitest'

const temporaryDirectories: string[] = []

async function makeDirectory(): Promise<string> {
  const directory = await mkdtemp(path.join(tmpdir(), 'cursebreaker-save-store-'))
  temporaryDirectories.push(directory)
  return directory
}

async function loadSaveStoreModule(): Promise<any> {
  const modulePath = '../../electron/save-store'
  return import(modulePath).catch(() => null)
}

afterEach(async () => {
  const { rm } = await import('node:fs/promises')
  await Promise.all(temporaryDirectories.splice(0).map((directory) => rm(directory, { recursive: true })))
})

describe('atomic save store', () => {
  test('returns null only when the save file is missing', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const store = new module.SaveStore({ directory: await makeDirectory() })

    await expect(store.loadSave()).resolves.toBeNull()
  })

  test('writes, reads, and overwrites one JSON document', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const store = new module.SaveStore({ directory: await makeDirectory() })

    await store.writeSave({ revision: 1, nested: ['safe', true, null] })
    await expect(store.loadSave()).resolves.toEqual({ revision: 1, nested: ['safe', true, null] })

    await store.writeSave({ revision: 2 })
    await expect(store.loadSave()).resolves.toEqual({ revision: 2 })
  })

  test('a failed atomic rename preserves the prior save and removes only its own temporary file', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory })
    await store.writeSave({ revision: 'prior' })
    await writeFile(path.join(directory, 'foreign.tmp'), 'not owned by the save store', 'utf8')
    const failingStore = new module.SaveStore({
      directory,
      fileOps: {
        rename: async () => {
          throw new Error('simulated rename failure')
        },
      },
    })

    await expect(failingStore.writeSave({ revision: 'new' })).rejects.toThrow('simulated rename failure')
    await expect(store.loadSave()).resolves.toEqual({ revision: 'prior' })
    await expect(readdir(directory)).resolves.toEqual(['foreign.tmp', 'save.json'])
  })

  test.each([
    ['undefined', undefined],
    ['a function', { callback: () => undefined }],
    ['a cycle', (() => { const value: Record<string, unknown> = {}; value.self = value; return value })()],
  ])('rejects %s before mutating the authoritative save', async (_label, invalidDocument) => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory })
    await store.writeSave({ revision: 'prior' })
    const before = await readFile(path.join(directory, 'save.json'), 'utf8')

    await expect(store.writeSave(invalidDocument)).rejects.toThrow()

    await expect(readFile(path.join(directory, 'save.json'), 'utf8')).resolves.toBe(before)
    await expect(readdir(directory)).resolves.toEqual(['save.json'])
  })

  test('rejects an oversized document before mutating the authoritative save', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory, maxBytes: 32 })
    await store.writeSave({ ok: true })
    const before = await readFile(path.join(directory, 'save.json'), 'utf8')

    await expect(store.writeSave({ text: 'x'.repeat(100) })).rejects.toThrow(/size/i)

    await expect(readFile(path.join(directory, 'save.json'), 'utf8')).resolves.toBe(before)
    await expect(readdir(directory)).resolves.toEqual(['save.json'])
  })
})
