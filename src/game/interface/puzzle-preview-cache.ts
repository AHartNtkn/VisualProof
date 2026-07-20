export type StoredPuzzlePreview = {
  readonly key: string
  readonly blob: Blob
  readonly lastUsed: number
}

export type PuzzlePreviewStorageBackend = {
  get(key: string): Promise<StoredPuzzlePreview | null>
  put(entry: StoredPuzzlePreview): Promise<void>
  list(): Promise<readonly StoredPuzzlePreview[]>
  delete(key: string): Promise<void>
  close(): void
}

export type PuzzlePreviewBlobStore = {
  get(key: string): Promise<Blob | null>
  put(key: string, blob: Blob): Promise<void>
  delete(key: string): Promise<void>
  dispose(): void
}

type ObjectUrlEntry = { readonly url: string; used: number }

export class ObjectUrlLru {
  readonly #limit: number
  readonly #create: (blob: Blob, key: string) => string
  readonly #revoke: (url: string) => void
  readonly #entries = new Map<string, ObjectUrlEntry>()
  #used = 0

  constructor(
    limit: number,
    create: (blob: Blob, key: string) => string,
    revoke: (url: string) => void,
  ) {
    this.#limit = limit
    this.#create = create
    this.#revoke = revoke
  }

  get(key: string): string | null {
    const entry = this.#entries.get(key)
    if (entry === undefined) return null
    entry.used = ++this.#used
    return entry.url
  }

  install(key: string, blob: Blob): string {
    const existing = this.#entries.get(key)
    if (existing !== undefined) {
      existing.used = ++this.#used
      return existing.url
    }
    const entry = { url: this.#create(blob, key), used: ++this.#used }
    this.#entries.set(key, entry)
    while (this.#entries.size > this.#limit) {
      let oldestKey: string | null = null
      let oldestUse = Number.POSITIVE_INFINITY
      for (const [candidateKey, candidate] of this.#entries) {
        if (candidate.used < oldestUse) {
          oldestKey = candidateKey
          oldestUse = candidate.used
        }
      }
      if (oldestKey === null) break
      const oldest = this.#entries.get(oldestKey)!
      this.#entries.delete(oldestKey)
      this.#revoke(oldest.url)
    }
    return entry.url
  }

  remove(key: string): void {
    const entry = this.#entries.get(key)
    if (entry === undefined) return
    this.#entries.delete(key)
    this.#revoke(entry.url)
  }

  dispose(): void {
    for (const { url } of this.#entries.values()) this.#revoke(url)
    this.#entries.clear()
  }
}

export class BoundedPersistentPreviewCache implements PuzzlePreviewBlobStore {
  readonly #backend: PuzzlePreviewStorageBackend
  readonly #now: () => number
  readonly #limit: number

  constructor(
    backend: PuzzlePreviewStorageBackend,
    now: () => number = Date.now,
    limit = 256,
  ) {
    this.#backend = backend
    this.#now = now
    this.#limit = limit
  }

  async get(key: string): Promise<Blob | null> {
    const entry = await this.#backend.get(key)
    if (entry === null) return null
    if (
      entry.key !== key
      || !(entry.blob instanceof Blob)
      || !Number.isFinite(entry.lastUsed)
    ) {
      await this.#backend.delete(key)
      return null
    }
    await this.#backend.put({ ...entry, lastUsed: this.#now() })
    return entry.blob
  }

  async put(key: string, blob: Blob): Promise<void> {
    await this.#backend.put({ key, blob, lastUsed: this.#now() })
    const entries = [...await this.#backend.list()]
      .sort((left, right) => left.lastUsed - right.lastUsed || left.key.localeCompare(right.key))
    const excess = entries.length - this.#limit
    for (let index = 0; index < excess; index += 1) {
      await this.#backend.delete(entries[index]!.key)
    }
  }

  async delete(key: string): Promise<void> {
    await this.#backend.delete(key)
  }

  dispose(): void {
    this.#backend.close()
  }
}

class UnavailablePreviewBackend implements PuzzlePreviewStorageBackend {
  async get(): Promise<StoredPuzzlePreview | null> { return null }
  async put(): Promise<void> {}
  async list(): Promise<readonly StoredPuzzlePreview[]> { return [] }
  async delete(): Promise<void> {}
  close(): void {}
}

class IndexedDbPreviewBackend implements PuzzlePreviewStorageBackend {
  readonly #database: Promise<IDBDatabase>

  constructor(factory: IDBFactory) {
    this.#database = new Promise((resolve, reject) => {
      const request = factory.open('cursebreaker-derived-previews', 1)
      request.onupgradeneeded = () => {
        const database = request.result
        if (!database.objectStoreNames.contains('previews')) {
          database.createObjectStore('previews', { keyPath: 'key' })
        }
      }
      request.onsuccess = () => resolve(request.result)
      request.onerror = () => reject(request.error ?? new Error('preview cache could not open'))
    })
  }

  async #request<T>(
    mode: IDBTransactionMode,
    operation: (store: IDBObjectStore) => IDBRequest<T>,
  ): Promise<T> {
    const database = await this.#database
    return new Promise((resolve, reject) => {
      const transaction = database.transaction('previews', mode)
      const request = operation(transaction.objectStore('previews'))
      request.onsuccess = () => resolve(request.result)
      request.onerror = () => reject(request.error ?? new Error('preview cache request failed'))
      transaction.onabort = () => reject(transaction.error ?? new Error('preview cache transaction aborted'))
    })
  }

  async get(key: string): Promise<StoredPuzzlePreview | null> {
    return (await this.#request('readonly', (store) => store.get(key)) as StoredPuzzlePreview | undefined)
      ?? null
  }

  async put(entry: StoredPuzzlePreview): Promise<void> {
    await this.#request('readwrite', (store) => store.put(entry))
  }

  async list(): Promise<readonly StoredPuzzlePreview[]> {
    return await this.#request('readonly', (store) => store.getAll()) as StoredPuzzlePreview[]
  }

  async delete(key: string): Promise<void> {
    await this.#request('readwrite', (store) => store.delete(key))
  }

  close(): void {
    void this.#database.then((database) => database.close(), () => {})
  }
}

export function createIndexedDbPuzzlePreviewCache(
  factory: IDBFactory | undefined = globalThis.indexedDB,
): PuzzlePreviewBlobStore {
  const backend = factory === undefined
    ? new UnavailablePreviewBackend()
    : new IndexedDbPreviewBackend(factory)
  return new BoundedPersistentPreviewCache(backend)
}
