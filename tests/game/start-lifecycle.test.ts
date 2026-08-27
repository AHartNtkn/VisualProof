import { describe, expect, it } from 'vitest'
import type { GameWorld } from '../../src/game/model'
import {
  PointerLockGate,
  StartLifecycle,
  type PointerLockPort,
  type StartFailure,
} from '../../src/game/start-lifecycle'

const world: GameWorld = {
  slot: { id: 'slot-a', name: 'Slot A', updatedAtMs: 1 },
  camera: { position: { x: 0, y: 1.7, z: 8 }, yaw: 0, pitch: -0.18 },
  trees: new Map(),
}

function deferred<T>(): {
  readonly promise: Promise<T>
  resolve(value: T): void
} {
  let resolve!: (value: T) => void
  const promise = new Promise<T>((done) => { resolve = done })
  return { promise, resolve }
}

async function until(predicate: () => boolean): Promise<void> {
  for (let attempts = 0; attempts < 20; attempts++) {
    if (predicate()) return
    await Promise.resolve()
  }
  throw new Error('condition did not become true')
}

class TestPointerLockPort implements PointerLockPort {
  public locked = false
  public releases = 0
  public readonly timeline: string[] = []
  public requestResult: void | Promise<void> = undefined
  private readonly changes = new Set<() => void>()
  private readonly errors = new Set<(error?: unknown) => void>()

  public get changeListenerCount(): number {
    return this.changes.size
  }

  public get errorListenerCount(): number {
    return this.errors.size
  }

  public request(): void | Promise<void> {
    this.timeline.push('request')
    return this.requestResult
  }

  public isLocked(): boolean {
    return this.locked
  }

  public onChange(listener: () => void): () => void {
    this.changes.add(listener)
    return () => this.changes.delete(listener)
  }

  public onError(listener: (error?: unknown) => void): () => void {
    this.errors.add(listener)
    return () => this.errors.delete(listener)
  }

  public release(): void {
    this.releases++
    this.locked = false
  }

  public acquire(): void {
    this.locked = true
    for (const listener of this.changes) listener()
  }

  public fail(error?: unknown): void {
    for (const listener of this.errors) listener(error)
  }
}

function lifecycleWith(
  port: TestPointerLockPort,
  opened: GameWorld[],
  failures: StartFailure[],
): StartLifecycle {
  return new StartLifecycle(new PointerLockGate(port), {
    open: (loaded) => { opened.push(loaded) },
    fail: (failure) => failures.push(failure),
  })
}

describe('game start lifecycle', () => {
  it('requests pointer lock synchronously and never constructs persistence after Promise rejection', async () => {
    const port = new TestPointerLockPort()
    port.requestResult = Promise.reject(new Error('permission denied'))
    const opened: GameWorld[] = []
    const failures: StartFailure[] = []
    const lifecycle = lifecycleWith(port, opened, failures)
    let persistenceCalls = 0

    const starting = lifecycle.start(async () => {
      persistenceCalls++
      return world
    })

    expect(port.timeline).toEqual(['request'])
    expect(persistenceCalls).toBe(0)
    await starting

    expect(persistenceCalls).toBe(0)
    expect(opened).toEqual([])
    expect(port.releases).toBe(1)
    expect(failures).toEqual([{ kind: 'pointer-lock', message: 'permission denied' }])
  })

  it('treats legacy pointerlockerror as failure without starting persistence', async () => {
    const port = new TestPointerLockPort()
    const opened: GameWorld[] = []
    const failures: StartFailure[] = []
    const lifecycle = lifecycleWith(port, opened, failures)
    let persistenceCalls = 0
    const starting = lifecycle.start(async () => {
      persistenceCalls++
      return world
    })

    port.fail()
    await starting

    expect(persistenceCalls).toBe(0)
    expect(opened).toEqual([])
    expect(failures).toEqual([{
      kind: 'pointer-lock', message: 'pointer lock was denied',
    }])
  })

  it('keeps controls rendered by a late slot list disabled and rejects overlapping factories', async () => {
    const port = new TestPointerLockPort()
    const opened: GameWorld[] = []
    const failures: StartFailure[] = []
    const lifecycle = lifecycleWith(port, opened, failures)
    const loading = deferred<GameWorld>()
    let firstCalls = 0
    let overlappingCalls = 0

    const starting = lifecycle.start(async () => {
      firstCalls++
      return loading.promise
    })
    port.acquire()
    await until(() => firstCalls === 1)

    const lateLoadButton = { disabled: false }
    lifecycle.registerControl(lateLoadButton)
    await lifecycle.start(async () => {
      overlappingCalls++
      throw new Error('overlapping load escaped its owner')
    })

    expect(lateLoadButton.disabled).toBe(true)
    expect(overlappingCalls).toBe(0)
    loading.resolve(world)
    await starting

    expect(opened).toEqual([world])
    expect(failures).toEqual([])
    expect(lateLoadButton.disabled).toBe(false)
  })

  it('invalidates a pending load before pagehide disposal can open a world', async () => {
    const port = new TestPointerLockPort()
    const opened: GameWorld[] = []
    const failures: StartFailure[] = []
    const loading = deferred<GameWorld>()
    let operationStarted = false
    let rendererTouches = 0
    let writersCreated = 0
    let framesRequested = 0
    const guarded = new StartLifecycle(new PointerLockGate(port), {
      open: (loaded) => {
        opened.push(loaded)
        rendererTouches++
        writersCreated++
        framesRequested++
      },
      fail: (failure) => failures.push(failure),
    })

    const starting = guarded.start(async () => {
      operationStarted = true
      return loading.promise
    })
    port.acquire()
    await until(() => operationStarted)

    guarded.dispose()
    loading.resolve(world)
    await starting

    expect(opened).toEqual([])
    expect(rendererTouches).toBe(0)
    expect(writersCreated).toBe(0)
    expect(framesRequested).toBe(0)
    expect(failures).toEqual([])
    expect(port.releases).toBe(1)
  })

  it('restores the menu after open throws and permits a later start', async () => {
    const port = new TestPointerLockPort()
    const failures: StartFailure[] = []
    const controls = { disabled: false }
    let openCalls = 0
    const lifecycle = new StartLifecycle(new PointerLockGate(port), {
      open: () => {
        openCalls++
        if (openCalls === 1) throw new Error('renderer initialization failed')
      },
      fail: (failure) => failures.push(failure),
    })
    lifecycle.registerControl(controls)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)

    const firstStart = lifecycle.start(async () => world)
    port.acquire()
    await firstStart

    expect(failures).toEqual([{
      kind: 'operation', message: 'renderer initialization failed',
    }])
    expect(port.locked).toBe(false)
    expect(port.releases).toBe(1)
    expect(controls.disabled).toBe(false)

    const retry = lifecycle.start(async () => world)
    expect(controls.disabled).toBe(true)
    port.acquire()
    await retry

    expect(openCalls).toBe(2)
    expect(failures).toHaveLength(1)
    expect(controls.disabled).toBe(false)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
  })

  it('cancels a Promise-backed acquisition and releases a late grant after disposal', async () => {
    const port = new TestPointerLockPort()
    const requested = deferred<void>()
    port.requestResult = requested.promise
    const lifecycle = lifecycleWith(port, [], [])
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    let operationCalls = 0
    let startSettled = false

    const starting = lifecycle.start(async () => {
      operationCalls++
      return world
    }).finally(() => { startSettled = true })
    lifecycle.dispose()
    await until(() => startSettled)

    expect(operationCalls).toBe(0)
    expect(port.releases).toBe(1)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)

    port.locked = true
    requested.resolve()
    await starting

    expect(port.locked).toBe(false)
    expect(port.releases).toBe(2)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
  })

  it('settles a cancelled legacy acquisition and rejects a late lock without listener growth', async () => {
    const port = new TestPointerLockPort()
    const lifecycle = lifecycleWith(port, [], [])
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    let operationCalls = 0
    let startSettled = false

    const starting = lifecycle.start(async () => {
      operationCalls++
      return world
    }).finally(() => { startSettled = true })
    lifecycle.dispose()
    await until(() => startSettled)

    expect(operationCalls).toBe(0)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)

    port.acquire()
    port.fail(new Error('late denial'))
    await starting

    expect(port.locked).toBe(false)
    expect(port.releases).toBe(2)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
  })
})
