import { describe, expect, it } from 'vitest'
import type { FreeCameraPose } from '../../src/game/model'
import type { CameraRecord, SaveClient, TreeUpdate } from '../../src/game/save-client'
import {
  SaveWriter,
  type SaveWriterClock,
  type SaveWriterStatus,
} from '../../src/game/save-writer'

type SavePort = Pick<SaveClient, 'updateTree' | 'updateCamera'>

function update(treeId: string, diagramJson: string): TreeUpdate {
  return { treeId, diagramJson, x: 1, z: 2, yaw: 3 }
}

function cameraAt(x: number): FreeCameraPose {
  return { position: { x, y: 1.7, z: 8 }, yaw: x / 10, pitch: -0.18 }
}

function cameraRecordAt(x: number): CameraRecord {
  return { x, y: 1.7, z: 8, yaw: x / 10, pitch: -0.18 }
}

async function until(predicate: () => boolean): Promise<void> {
  for (let attempts = 0; attempts < 20; attempts++) {
    if (predicate()) return
    await Promise.resolve()
  }
  throw new Error('condition did not become true')
}

function deferredSavePort(): SavePort & {
  readonly treeWrites: TreeUpdate[]
  readonly cameraWrites: CameraRecord[]
  readonly started: string[]
  resolveNext(): void
} {
  const treeWrites: TreeUpdate[] = []
  const cameraWrites: CameraRecord[] = []
  const started: string[] = []
  const resolutions: (() => void)[] = []
  const block = (label: string): Promise<void> => {
    started.push(label)
    return new Promise((resolve) => resolutions.push(resolve))
  }
  return {
    treeWrites,
    cameraWrites,
    started,
    updateTree: async (_slotId, value) => {
      treeWrites.push(value)
      await block(`tree:${value.treeId}:${value.diagramJson}`)
      return 1
    },
    updateCamera: async (_slotId, value) => {
      cameraWrites.push(value)
      await block(`camera:${value.x}`)
    },
    resolveNext() {
      const resolve = resolutions.shift()
      if (resolve === undefined) throw new Error('no write is waiting')
      resolve()
    },
  }
}

class FakeClock implements SaveWriterClock {
  private now = 0
  private nextId = 1
  private readonly scheduled = new Map<number, { readonly at: number; readonly run: () => void }>()

  public setTimeout(run: () => void, milliseconds: number): number {
    const id = this.nextId++
    this.scheduled.set(id, { at: this.now + milliseconds, run })
    return id
  }

  public clearTimeout(id: unknown): void {
    this.scheduled.delete(id as number)
  }

  public advance(milliseconds: number): void {
    this.now += milliseconds
    for (;;) {
      const due = [...this.scheduled.entries()]
        .filter(([, task]) => task.at <= this.now)
        .sort((left, right) => left[1].at - right[1].at || left[0] - right[0])[0]
      if (due === undefined) return
      this.scheduled.delete(due[0])
      due[1].run()
    }
  }
}

describe('ordered save writer', () => {
  it('orders writes per slot and coalesces only pending snapshots for the same tree', async () => {
    const port = deferredSavePort()
    const writer = new SaveWriter('slot-a', port)
    writer.tree(update('a', 'one'))
    await until(() => port.started.length === 1)
    writer.tree(update('a', 'two'))
    writer.tree(update('a', 'three'))
    writer.tree(update('b', 'other'))

    expect(port.started).toEqual(['tree:a:one'])
    port.resolveNext()
    await until(() => port.started.length === 2)
    expect(port.started).toEqual(['tree:a:one', 'tree:a:three'])
    port.resolveNext()
    await until(() => port.started.length === 3)
    port.resolveNext()
    await writer.flush()

    expect(port.treeWrites.map(({ treeId, diagramJson }) => [treeId, diagramJson]))
      .toEqual([['a', 'one'], ['a', 'three'], ['b', 'other']])
  })

  it('debounces camera changes for 500 ms and writes the newest displayed free pose', async () => {
    const clock = new FakeClock()
    const cameraWrites: CameraRecord[] = []
    const port: SavePort = {
      updateTree: async () => 1,
      updateCamera: async (_slotId, camera) => { cameraWrites.push(camera) },
    }
    const writer = new SaveWriter('slot-a', port, clock)

    writer.camera(cameraAt(1))
    clock.advance(499)
    expect(cameraWrites).toEqual([])
    writer.camera(cameraAt(2))
    clock.advance(499)
    expect(cameraWrites).toEqual([])
    clock.advance(1)
    await writer.flush()

    expect(cameraWrites).toEqual([cameraRecordAt(2)])
  })

  it('does not postpone or repeat persistence when the same displayed camera arrives every frame', async () => {
    const clock = new FakeClock()
    const cameraWrites: CameraRecord[] = []
    const port: SavePort = {
      updateTree: async () => 1,
      updateCamera: async (_slotId, camera) => { cameraWrites.push(camera) },
    }
    const writer = new SaveWriter('slot-a', port, clock)

    for (let elapsed = 0; elapsed < 500; elapsed += 100) {
      writer.camera(cameraAt(3))
      clock.advance(100)
    }
    await writer.flush()
    expect(cameraWrites).toEqual([cameraRecordAt(3)])

    writer.camera(cameraAt(3))
    clock.advance(500)
    await writer.flush()
    expect(cameraWrites).toEqual([cameraRecordAt(3)])
  })

  it('keeps the newest unsaved tree state and a persistent error until new state retries it', async () => {
    const attempts: TreeUpdate[] = []
    let failuresRemaining = 1
    const port: SavePort = {
      updateTree: async (_slotId, value) => {
        attempts.push(value)
        if (failuresRemaining-- > 0) throw new Error('database unavailable')
        return 1
      },
      updateCamera: async () => {},
    }
    const writer = new SaveWriter('slot-a', port)
    const statuses: SaveWriterStatus[] = []
    writer.subscribe((status) => statuses.push(status))

    writer.tree(update('a', 'one'))
    writer.tree(update('a', 'newest'))
    await writer.flush()

    expect(attempts.map(({ diagramJson }) => diagramJson)).toEqual(['one'])
    expect(statuses.at(-1)).toEqual({ state: 'error', message: 'database unavailable' })

    writer.tree(update('b', 'other'))
    await writer.flush()

    expect(attempts.map(({ treeId, diagramJson }) => [treeId, diagramJson])).toEqual([
      ['a', 'one'],
      ['a', 'newest'],
      ['b', 'other'],
    ])
    expect(statuses.at(-1)).toEqual({ state: 'idle' })
  })

  it('retries a failed camera explicitly without clearing the error early', async () => {
    const clock = new FakeClock()
    let failuresRemaining = 1
    const writes: CameraRecord[] = []
    const port: SavePort = {
      updateTree: async () => 1,
      updateCamera: async (_slotId, camera) => {
        writes.push(camera)
        if (failuresRemaining-- > 0) throw new Error('camera write failed')
      },
    }
    const writer = new SaveWriter('slot-a', port, clock)
    const statuses: SaveWriterStatus[] = []
    writer.subscribe((status) => statuses.push(status))

    writer.camera(cameraAt(4))
    clock.advance(500)
    await writer.flush()
    expect(statuses.at(-1)).toEqual({ state: 'error', message: 'camera write failed' })

    writer.retry()
    expect(statuses.at(-1)).toEqual({ state: 'saving' })
    await writer.flush()

    expect(writes).toEqual([cameraRecordAt(4), cameraRecordAt(4)])
    expect(statuses.at(-1)).toEqual({ state: 'idle' })
  })

  it('dispose forces debounced state, waits for every accepted write, then rejects new state', async () => {
    const clock = new FakeClock()
    const port = deferredSavePort()
    const writer = new SaveWriter('slot-a', port, clock)
    writer.tree(update('a', 'one'))
    writer.camera(cameraAt(7))
    const disposing = writer.dispose()

    await until(() => port.started.length === 1)
    expect(port.started).toEqual(['tree:a:one'])
    port.resolveNext()
    await until(() => port.started.length === 2)
    expect(port.started).toEqual(['tree:a:one', 'camera:7'])
    port.resolveNext()
    await disposing

    expect(() => writer.tree(update('b', 'late'))).toThrow('disposed')
    expect(() => writer.camera(cameraAt(8))).toThrow('disposed')
  })

  it('a failed dispose reports the write error and leaves retained state retryable', async () => {
    let fail = true
    const attempts: TreeUpdate[] = []
    const port: SavePort = {
      updateTree: async (_slotId, value) => {
        attempts.push(value)
        if (fail) throw new Error('disk full')
        return 1
      },
      updateCamera: async () => {},
    }
    const writer = new SaveWriter('slot-a', port)
    writer.tree(update('a', 'one'))
    await writer.flush()

    await expect(writer.dispose()).rejects.toThrow('disk full')
    fail = false
    writer.retry()
    await writer.flush()
    await writer.dispose()

    expect(attempts).toEqual([update('a', 'one'), update('a', 'one'), update('a', 'one')])
  })

  it('shares concurrent disposal while a macrotask-backed write is in flight', async () => {
    let attempts = 0
    const port: SavePort = {
      updateTree: async () => {
        attempts++
        await new Promise<void>((resolve) => setTimeout(resolve, 0))
        return 1
      },
      updateCamera: async () => {},
    }
    const writer = new SaveWriter('slot-a', port)
    writer.tree(update('a', 'one'))

    const first = writer.dispose()
    const second = writer.dispose()
    expect(second).toBe(first)
    await Promise.all([first, second])

    expect(attempts).toBe(1)
    expect(() => writer.tree(update('b', 'late'))).toThrow('disposed')
  })
})
