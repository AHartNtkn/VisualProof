import { mkdtemp, open, readFile, readdir, unlink, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { afterEach, describe, expect, test, vi } from 'vitest'

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

  test('returns malformed JSON as a rejected document so game recovery can quarantine it', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory })
    await writeFile(path.join(directory, 'save.json'), '{"broken":', 'utf8')

    await expect(store.loadSave()).resolves.toBe('{"broken":')
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

  test('quarantines a rejected document before installing its validated replacement', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory })
    const rejected = { format: 'cursebreaker-save', version: 3, acknowledgedTeachers: ['old'] }
    const replacement = { format: 'cursebreaker-save', version: 4 }
    await store.writeSave(rejected)

    await store.replaceInvalidSave(replacement)

    await expect(store.loadSave()).resolves.toEqual(replacement)
    const files = await readdir(directory)
    expect(files).toContain('save.json')
    const quarantined = files.filter((name) => /^rejected-save-[\da-f-]+\.json$/.test(name))
    expect(quarantined).toHaveLength(1)
    await expect(readFile(path.join(directory, quarantined[0]!), 'utf8'))
      .resolves.toBe(JSON.stringify(rejected))
  })

  test('does not create a replacement when there is no rejected authoritative save', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory })

    await expect(store.replaceInvalidSave({ revision: 4 })).rejects.toThrow(/no authoritative save/i)

    await expect(readdir(directory)).resolves.toEqual([])
  })

  test('never overwrites an existing quarantine artifact on a name collision', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const store = new module.SaveStore({ directory, quarantineId: () => 'collision' })
    await store.writeSave({ revision: 3 })
    const collisionPath = path.join(directory, 'rejected-save-collision.json')
    await writeFile(collisionPath, 'foreign retained evidence', 'utf8')

    await expect(store.replaceInvalidSave({ revision: 4 })).rejects.toMatchObject({ code: 'EEXIST' })

    await expect(store.loadSave()).resolves.toEqual({ revision: 3 })
    await expect(readFile(collisionPath, 'utf8')).resolves.toBe('foreign retained evidence')
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

  test('an exclusive-open collision never unlinks a temporary file it did not create', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const collision = Object.assign(new Error('simulated exclusive-open collision'), { code: 'EEXIST' })
    const unlinkSpy = vi.fn(async () => undefined)
    const store = new module.SaveStore({
      directory,
      fileOps: {
        open: vi.fn(async () => { throw collision }),
        unlink: unlinkSpy,
      },
    })

    await expect(store.writeSave({ revision: 1 })).rejects.toBe(collision)
    expect(unlinkSpy).not.toHaveBeenCalled()
  })

  test('a temporary close failure still cleans up its owned temp without swallowing the primary error', async () => {
    const module = await loadSaveStoreModule()
    expect(module).not.toBeNull()
    const directory = await makeDirectory()
    const closeFailure = new Error('simulated temporary close failure')
    const unlinkedPaths: string[] = []
    const store = new module.SaveStore({
      directory,
      fileOps: {
        open: async (...arguments_: Parameters<typeof open>) => {
          const handle = await open(...arguments_)
          const openedPath = String(arguments_[0])
          if (!path.basename(openedPath).startsWith('.save-')) return handle
          let physicallyClosed = false
          return new Proxy(handle, {
            get(target, property) {
              if (property === 'close') {
                return async () => {
                  if (!physicallyClosed) {
                    physicallyClosed = true
                    await target.close()
                  }
                  throw closeFailure
                }
              }
              const value = Reflect.get(target, property, target)
              return typeof value === 'function' ? value.bind(target) : value
            },
          })
        },
        unlink: async (target: Parameters<typeof unlink>[0]) => {
          unlinkedPaths.push(String(target))
          await unlink(target)
        },
      },
    })

    await expect(store.writeSave({ revision: 1 })).rejects.toBe(closeFailure)
    expect(unlinkedPaths).toHaveLength(1)
    expect(path.basename(unlinkedPaths[0] ?? '')).toMatch(/^\.save-.*\.tmp$/)
    await expect(readdir(directory)).resolves.toEqual([])
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
