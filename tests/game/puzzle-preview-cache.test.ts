import { describe, expect, it } from 'vitest'
import {
  BoundedPersistentPreviewCache,
  ObjectUrlLru,
  type PuzzlePreviewStorageBackend,
  type StoredPuzzlePreview,
} from '../../src/game/interface/puzzle-preview-cache'

class MemoryBackend implements PuzzlePreviewStorageBackend {
  readonly entries = new Map<string, StoredPuzzlePreview>()

  async get(key: string): Promise<StoredPuzzlePreview | null> {
    return this.entries.get(key) ?? null
  }

  async put(entry: StoredPuzzlePreview): Promise<void> {
    this.entries.set(entry.key, entry)
  }

  async list(): Promise<readonly StoredPuzzlePreview[]> {
    return [...this.entries.values()]
  }

  async delete(key: string): Promise<void> {
    this.entries.delete(key)
  }

  close(): void {}
}

describe('puzzle preview caches', () => {
  it('revokes the least-recently-used decoded URL at the exact memory bound', () => {
    const revoked: string[] = []
    let nextUrl = 0
    const cache = new ObjectUrlLru(24, () => `blob:${nextUrl++}`, (url) => revoked.push(url))
    for (let index = 0; index < 24; index += 1) {
      cache.install(`key-${index}`, new Blob([String(index)]))
    }
    expect(cache.get('key-0')).toBe('blob:0')

    cache.install('key-24', new Blob(['24']))

    expect(revoked).toEqual(['blob:1'])
    expect(cache.get('key-1')).toBeNull()
    expect(cache.get('key-0')).toBe('blob:0')
    cache.dispose()
    expect(new Set(revoked).size).toBe(25)
  })

  it('keeps only the 256 most recently used persistent PNGs', async () => {
    const backend = new MemoryBackend()
    let now = 0
    const cache = new BoundedPersistentPreviewCache(backend, () => ++now, 256)
    for (let index = 0; index < 257; index += 1) {
      await cache.put(`key-${index}`, new Blob([String(index)], { type: 'image/png' }))
    }

    expect(backend.entries.size).toBe(256)
    expect(backend.entries.has('key-0')).toBe(false)
    expect(backend.entries.has('key-256')).toBe(true)

    await cache.get('key-1')
    await cache.put('key-257', new Blob(['257'], { type: 'image/png' }))
    expect(backend.entries.has('key-1')).toBe(true)
    expect(backend.entries.has('key-2')).toBe(false)
  })

  it('deletes a structurally invalid persistent entry instead of returning it', async () => {
    const backend = new MemoryBackend()
    backend.entries.set('bad', {
      key: 'bad',
      blob: 'not a blob' as unknown as Blob,
      lastUsed: 1,
    })
    const cache = new BoundedPersistentPreviewCache(backend)

    expect(await cache.get('bad')).toBeNull()
    expect(backend.entries.has('bad')).toBe(false)
  })
})
