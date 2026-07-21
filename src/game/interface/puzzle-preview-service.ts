import type {
  PuzzlePreviewRequest,
  PuzzlePreviewWorkerRequest,
  PuzzlePreviewWorkerResult,
} from './puzzle-preview-contract'
import {
  PUZZLE_PREVIEW_HEIGHT,
  PUZZLE_PREVIEW_WIDTH,
} from './puzzle-preview-contract'
import {
  createIndexedDbPuzzlePreviewCache,
  ObjectUrlLru,
  type PuzzlePreviewBlobStore,
} from './puzzle-preview-cache'

export type { PuzzlePreviewBlobStore } from './puzzle-preview-cache'

export type PuzzlePreviewState =
  | { readonly kind: 'preparing' }
  | { readonly kind: 'ready'; readonly url: string }
  | { readonly kind: 'error'; readonly message: string }

export type PuzzlePreviewWorkerPort = {
  onmessage: ((event: MessageEvent<PuzzlePreviewWorkerResult>) => void) | null
  onerror: ((event: ErrorEvent) => void) | null
  onmessageerror: ((event: MessageEvent<unknown>) => void) | null
  postMessage(message: PuzzlePreviewWorkerRequest): void
  terminate(): void
}
export type PuzzlePreviewService = {
  subscribe(
    request: PuzzlePreviewRequest,
    listener: (state: PuzzlePreviewState) => void,
  ): () => void
  currentUrl(key: string): string | null
  invalidate(key: string): void
  dispose(): void
}

type PreviewEntry = {
  readonly request: PuzzlePreviewRequest
  readonly listeners: Set<(state: PuzzlePreviewState) => void>
  state: PuzzlePreviewState
  phase: 'cache' | 'queued' | 'rendering'
}

type PuzzlePreviewServiceOptions = {
  readonly store: PuzzlePreviewBlobStore
  readonly worker: PuzzlePreviewWorkerPort
  readonly restartWorker?: () => PuzzlePreviewWorkerPort
  readonly createObjectUrl: (blob: Blob, key: string) => string
  readonly revokeObjectUrl: (url: string) => void
  readonly validateBlob?: (blob: Blob) => Promise<boolean>
}

export function createPuzzlePreviewService(
  options: PuzzlePreviewServiceOptions,
): PuzzlePreviewService {
  const decoded = new ObjectUrlLru(24, options.createObjectUrl, options.revokeObjectUrl)
  const entries = new Map<string, PreviewEntry>()
  const queue: PreviewEntry[] = []
  let active: { readonly entry: PreviewEntry; readonly generation: number } | null = null
  let worker: PuzzlePreviewWorkerPort | null = options.worker
  let generation = 0
  let disposed = false

  const publish = (entry: PreviewEntry, state: PuzzlePreviewState): void => {
    entry.state = state
    for (const listener of entry.listeners) listener(state)
  }

  const pump = (): void => {
    if (disposed || active !== null) return
    while (queue.length > 0) {
      const entry = queue.shift()!
      if (entry.listeners.size === 0 || entries.get(entry.request.key) !== entry) {
        if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
        continue
      }
      entry.phase = 'rendering'
      const requestGeneration = ++generation
      active = { entry, generation: requestGeneration }
      try {
        if (worker === null) {
          if (options.restartWorker === undefined) {
            throw new Error('preview worker is unavailable')
          }
          worker = options.restartWorker()
          bindWorker(worker)
        }
        worker.postMessage({
          kind: 'render',
          generation: requestGeneration,
          request: entry.request,
        })
        return
      } catch (error) {
        active = null
        publish(entry, {
          kind: 'error',
          message: error instanceof Error ? error.message : String(error),
        })
        if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
      }
    }
  }

  const receiveWorkerMessage = (event: MessageEvent<PuzzlePreviewWorkerResult>): void => {
    const current = active
    if (disposed || current === null
      || event.data.generation !== current.generation
      || event.data.key !== current.entry.request.key) return
    active = null
    const entry = current.entry
    if (event.data.kind === 'error') {
      if (entry.listeners.size > 0) publish(entry, { kind: 'error', message: event.data.message })
      if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
      pump()
      return
    }
    const { blob } = event.data
    void options.store.put(entry.request.key, blob).catch(() => {})
    if (entry.listeners.size > 0) {
      try {
        const url = decoded.install(entry.request.key, blob)
        publish(entry, { kind: 'ready', url })
      } catch (error) {
        publish(entry, {
          kind: 'error',
          message: error instanceof Error ? error.message : String(error),
        })
      }
    }
    if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
    pump()
  }

  const failActive = (message: string): void => {
    const current = active
    if (disposed) return
    if (current !== null) {
      active = null
      const entry = current.entry
      if (entry.listeners.size > 0) {
        publish(entry, {
          kind: 'error',
          message,
        })
      }
      if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
    }
    pump()
  }

  const bindWorker = (target: PuzzlePreviewWorkerPort): void => {
    target.onmessage = receiveWorkerMessage
    target.onerror = (event): void => {
      if (disposed || worker !== target) return
      target.onmessage = null
      target.onerror = null
      target.onmessageerror = null
      target.terminate()
      worker = null
      failActive(event.message.length > 0 ? event.message : 'preview worker failed')
    }
    target.onmessageerror = (): void => {
      if (worker === target) failActive('preview worker returned unreadable data')
    }
  }

  const load = async (entry: PreviewEntry): Promise<void> => {
    let blob: Blob | null = null
    try {
      blob = await options.store.get(entry.request.key)
    } catch {
      blob = null
    }
    if (disposed || entries.get(entry.request.key) !== entry) return
    if (entry.listeners.size === 0) {
      if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
      return
    }
    if (blob !== null && options.validateBlob !== undefined) {
      let valid = false
      try {
        valid = await options.validateBlob(blob)
      } catch {
        valid = false
      }
      if (disposed || entries.get(entry.request.key) !== entry) return
      if (!valid) {
        await options.store.delete(entry.request.key).catch(() => {})
        if (disposed || entries.get(entry.request.key) !== entry) return
        blob = null
      }
    }
    if (blob !== null) {
      try {
        publish(entry, { kind: 'ready', url: decoded.install(entry.request.key, blob) })
        if (entries.get(entry.request.key) === entry) entries.delete(entry.request.key)
        return
      } catch {
        await options.store.delete(entry.request.key).catch(() => {})
        if (disposed || entries.get(entry.request.key) !== entry) return
      }
    }
    entry.phase = 'queued'
    queue.push(entry)
    pump()
  }

  bindWorker(worker)

  return {
    subscribe(request, listener) {
      if (disposed) {
        listener({ kind: 'error', message: 'preview service is disposed' })
        return () => {}
      }
      const ready = decoded.get(request.key)
      if (ready !== null) {
        listener({ kind: 'ready', url: ready })
        return () => {}
      }
      let entry = entries.get(request.key)
      if (entry === undefined) {
        entry = {
          request,
          listeners: new Set(),
          state: { kind: 'preparing' },
          phase: 'cache',
        }
        entries.set(request.key, entry)
        void load(entry)
      }
      entry.listeners.add(listener)
      listener(entry.state)
      const subscribedEntry = entry
      return () => {
        subscribedEntry.listeners.delete(listener)
        if (subscribedEntry.listeners.size === 0 && subscribedEntry.phase !== 'rendering') {
          if (entries.get(subscribedEntry.request.key) === subscribedEntry) {
            entries.delete(subscribedEntry.request.key)
          }
        }
      }
    },
    currentUrl(key) {
      return decoded.get(key)
    },
    invalidate(key) {
      decoded.remove(key)
      void options.store.delete(key).catch(() => {})
    },
    dispose() {
      if (disposed) return
      disposed = true
      generation += 1
      active = null
      queue.length = 0
      entries.clear()
      if (worker !== null) {
        worker.onmessage = null
        worker.onerror = null
        worker.onmessageerror = null
        worker.terminate()
        worker = null
      }
      decoded.dispose()
      options.store.dispose()
    },
  }
}

export function createBrowserPuzzlePreviewService(): PuzzlePreviewService {
  const createWorker = (): Worker => new Worker(
    new URL('./puzzle-preview.worker.ts', import.meta.url),
    { type: 'module' },
  )
  return createPuzzlePreviewService({
    worker: createWorker(),
    restartWorker: createWorker,
    store: createIndexedDbPuzzlePreviewCache(),
    createObjectUrl: (blob) => URL.createObjectURL(blob),
    revokeObjectUrl: (url) => URL.revokeObjectURL(url),
    validateBlob: async (blob) => {
      if (blob.type !== 'image/png') return false
      const bitmap = await createImageBitmap(blob)
      try {
        return bitmap.width === PUZZLE_PREVIEW_WIDTH && bitmap.height === PUZZLE_PREVIEW_HEIGHT
      } finally {
        bitmap.close()
      }
    },
  })
}
