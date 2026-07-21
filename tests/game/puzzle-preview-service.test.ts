import { describe, expect, it } from 'vitest'
import type {
  PuzzlePreviewRequest,
  PuzzlePreviewWorkerRequest,
  PuzzlePreviewWorkerResult,
} from '../../src/game/interface/puzzle-preview-contract'
import {
  createPuzzlePreviewService,
  type PuzzlePreviewBlobStore,
  type PuzzlePreviewState,
  type PuzzlePreviewWorkerPort,
} from '../../src/game/interface/puzzle-preview-service'

const request = (key: string): PuzzlePreviewRequest => ({
  key,
  fingerprint: key,
  diagram: { root: 'root', regions: {}, nodes: {}, wires: {} },
  width: 640,
  height: 400,
})
class MemoryStore implements PuzzlePreviewBlobStore {
  readonly values = new Map<string, Blob>()
  readonly gets: string[] = []
  readonly puts: string[] = []
  readonly deletes: string[] = []

  async get(key: string): Promise<Blob | null> {
    this.gets.push(key)
    return this.values.get(key) ?? null
  }

  async put(key: string, blob: Blob): Promise<void> {
    this.puts.push(key)
    this.values.set(key, blob)
  }

  async delete(key: string): Promise<void> {
    this.deletes.push(key)
    this.values.delete(key)
  }

  dispose(): void {}
}

class FakeWorker implements PuzzlePreviewWorkerPort {
  readonly posted: PuzzlePreviewWorkerRequest[] = []
  terminated = false
  onmessage: ((event: MessageEvent<PuzzlePreviewWorkerResult>) => void) | null = null
  onerror: ((event: ErrorEvent) => void) | null = null
  onmessageerror: ((event: MessageEvent<unknown>) => void) | null = null
  postFailure: Error | null = null

  postMessage(message: PuzzlePreviewWorkerRequest): void {
    if (this.postFailure !== null) throw this.postFailure
    this.posted.push(message)
  }

  emit(result: PuzzlePreviewWorkerResult): void {
    this.onmessage?.({ data: result } as MessageEvent<PuzzlePreviewWorkerResult>)
  }

  emitError(message: string): void {
    this.onerror?.({ message } as ErrorEvent)
  }


  emitMessageError(): void {
    this.onmessageerror?.({ data: null } as MessageEvent<unknown>)
  }

  terminate(): void {
    this.terminated = true
  }
}

const flush = async (): Promise<void> => {
  await Promise.resolve()
  await Promise.resolve()
  await Promise.resolve()
}

describe('puzzle preview service', () => {
  it('serves a persistent hit without worker work', async () => {
    const store = new MemoryStore()
    store.values.set('cached', new Blob(['cached']))
    const worker = new FakeWorker()
    const states: PuzzlePreviewState[] = []
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: () => 'blob:cached',
      revokeObjectUrl: () => {},
    })

    service.subscribe(request('cached'), (state) => states.push(state))
    await flush()

    expect(states).toEqual([{ kind: 'preparing' }, { kind: 'ready', url: 'blob:cached' }])
    expect(worker.posted).toEqual([])
    service.dispose()
  })

  it('deduplicates subscribers and cancels queued work with no listeners', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: () => {},
    })
    const first: PuzzlePreviewState[] = []
    const second: PuzzlePreviewState[] = []
    service.subscribe(request('shared'), (state) => first.push(state))
    service.subscribe(request('shared'), (state) => second.push(state))
    const cancelQueued = service.subscribe(request('queued'), () => {})
    cancelQueued()
    await flush()

    expect(worker.posted.map(({ request: value }) => value.key)).toEqual(['shared'])
    const active = worker.posted[0]!
    worker.emit({ kind: 'ready', key: 'shared', generation: active.generation, blob: new Blob(['png']) })
    await flush()

    expect(first.at(-1)).toEqual({ kind: 'ready', url: 'blob:shared' })
    expect(second.at(-1)).toEqual({ kind: 'ready', url: 'blob:shared' })
    expect(store.puts).toEqual(['shared'])
    service.dispose()
  })

  it('does not let a cancelled queued entry delete a replacement for the same key', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: () => {},
    })
    service.subscribe(request('active'), () => {})
    await flush()
    const cancel = service.subscribe(request('replacement'), () => {})
    await flush()
    cancel()
    const replacement: PuzzlePreviewState[] = []
    service.subscribe(request('replacement'), (state) => replacement.push(state))
    await flush()

    const active = worker.posted[0]!
    worker.emit({ kind: 'ready', key: 'active', generation: active.generation, blob: new Blob(['png']) })
    await flush()

    expect(worker.posted.map(({ request: value }) => value.key)).toEqual(['active', 'replacement'])
    const postedReplacement = worker.posted[1]!
    worker.emit({
      kind: 'ready',
      key: 'replacement',
      generation: postedReplacement.generation,
      blob: new Blob(['replacement']),
    })
    expect(replacement.at(-1)).toEqual({ kind: 'ready', url: 'blob:replacement' })
    service.dispose()
  })

  it('reports worker failure and rejects stale generations after disposal', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const states: PuzzlePreviewState[] = []
    const revoked: string[] = []
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: (url) => revoked.push(url),
    })
    service.subscribe(request('broken'), (state) => states.push(state))
    await flush()
    const active = worker.posted[0]!
    worker.emit({ kind: 'error', key: 'broken', generation: active.generation, message: 'bad diagram' })
    expect(states.at(-1)).toEqual({ kind: 'error', message: 'bad diagram' })

    service.subscribe(request('late'), () => {})
    await flush()
    const late = worker.posted[1]!
    service.dispose()
    worker.emit({ kind: 'ready', key: 'late', generation: late.generation, blob: new Blob(['late']) })
    await flush()
    expect(store.puts).toEqual([])
    expect(revoked).toEqual([])
    expect(worker.terminated).toBe(true)
  })

  it('reports a worker process failure and continues with the next preview', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const replacement = new FakeWorker()
    const failed: PuzzlePreviewState[] = []
    const next: PuzzlePreviewState[] = []
    const service = createPuzzlePreviewService({
      store,
      worker,
      restartWorker: () => replacement,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: () => {},
    })

    service.subscribe(request('failed'), (state) => failed.push(state))
    service.subscribe(request('next'), (state) => next.push(state))
    await flush()
    worker.emitError('worker crashed')

    expect(failed.at(-1)).toEqual({ kind: 'error', message: 'worker crashed' })
    expect(worker.posted.map(({ request: value }) => value.key)).toEqual(['failed'])
    expect(worker.terminated).toBe(true)
    expect(replacement.posted.map(({ request: value }) => value.key)).toEqual(['next'])
    const posted = replacement.posted[0]!
    replacement.emit({
      kind: 'ready',
      key: 'next',
      generation: posted.generation,
      blob: new Blob(['next']),
    })
    expect(next.at(-1)).toEqual({ kind: 'ready', url: 'blob:next' })
    service.dispose()
  })

  it('handles synchronous posting and worker message decoding failures without stalling', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const failed: PuzzlePreviewState[] = []
    worker.postFailure = new Error('could not clone')
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: () => {},
    })
    service.subscribe(request('post-failure'), (state) => failed.push(state))
    await flush()
    expect(failed.at(-1)).toEqual({ kind: 'error', message: 'could not clone' })

    worker.postFailure = null
    const unreadable: PuzzlePreviewState[] = []
    service.subscribe(request('unreadable'), (state) => unreadable.push(state))
    await flush()
    worker.emitMessageError()
    expect(unreadable.at(-1)).toEqual({
      kind: 'error',
      message: 'preview worker returned unreadable data',
    })
    service.dispose()
  })

  it('deletes and regenerates a cached blob that fails image validation', async () => {
    const store = new MemoryStore()
    store.values.set('corrupt', new Blob(['not a png']))
    const worker = new FakeWorker()
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => `blob:${key}`,
      revokeObjectUrl: () => {},
      validateBlob: async () => false,
    })
    service.subscribe(request('corrupt'), () => {})
    await flush()

    expect(store.deletes).toEqual(['corrupt'])
    expect(worker.posted.map(({ request: value }) => value.key)).toEqual(['corrupt'])
    service.dispose()
  })

  it('reports object URL creation failure without stalling queued work', async () => {
    const store = new MemoryStore()
    const worker = new FakeWorker()
    const failed: PuzzlePreviewState[] = []
    const next: PuzzlePreviewState[] = []
    let urlFailure = true
    const service = createPuzzlePreviewService({
      store,
      worker,
      createObjectUrl: (_blob, key) => {
        if (urlFailure) throw new Error('object URL unavailable')
        return `blob:${key}`
      },
      revokeObjectUrl: () => {},
    })
    service.subscribe(request('url-failure'), (state) => failed.push(state))
    service.subscribe(request('after-url-failure'), (state) => next.push(state))
    await flush()
    const first = worker.posted[0]!

    expect(() => worker.emit({
      kind: 'ready',
      key: 'url-failure',
      generation: first.generation,
      blob: new Blob(['png']),
    })).not.toThrow()
    expect(failed.at(-1)).toEqual({ kind: 'error', message: 'object URL unavailable' })
    urlFailure = false
    const second = worker.posted[1]!
    worker.emit({
      kind: 'ready',
      key: 'after-url-failure',
      generation: second.generation,
      blob: new Blob(['png']),
    })
    expect(next.at(-1)).toEqual({ kind: 'ready', url: 'blob:after-url-failure' })
    service.dispose()
  })
})
