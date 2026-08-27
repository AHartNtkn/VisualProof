import { describe, expect, it } from 'vitest'
import type { GameWorld } from '../../src/game/model'
import {
  PointerLockGate,
  ResumePointerLock,
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
  reject(error: unknown): void
} {
  let resolve!: (value: T) => void
  let reject!: (error: unknown) => void
  const promise = new Promise<T>((done, fail) => {
    resolve = done
    reject = fail
  })
  return { promise, resolve, reject }
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
  public requestError: unknown | null = null
  public releaseError: unknown | null = null
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
    if (this.requestError !== null) throw this.requestError
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
    if (this.releaseError !== null) throw this.releaseError
  }

  public acquire(): void {
    this.locked = true
    for (const listener of this.changes) listener()
  }

  public unlock(): void {
    this.locked = false
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
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
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
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
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
    expect(port.locked).toBe(true)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
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
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    const firstStart = lifecycle.start(async () => world)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.acquire()
    await firstStart

    expect(failures).toEqual([{
      kind: 'operation', message: 'renderer initialization failed',
    }])
    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    expect(controls.disabled).toBe(false)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    const retry = lifecycle.start(async () => world)
    expect(controls.disabled).toBe(true)
    port.acquire()
    await retry

    expect(openCalls).toBe(2)
    expect(failures).toHaveLength(1)
    expect(controls.disabled).toBe(false)
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('restores the menu after asynchronous open rejection and permits a later start', async () => {
    const port = new TestPointerLockPort()
    const opening = deferred<void>()
    const failures: StartFailure[] = []
    let openCalls = 0
    const lifecycle = new StartLifecycle(new PointerLockGate(port), {
      open: () => {
        openCalls++
        return openCalls === 1 ? opening.promise : undefined
      },
      fail: (failure) => failures.push(failure),
    })

    const firstStart = lifecycle.start(async () => world)
    port.acquire()
    await until(() => openCalls === 1)
    opening.reject(new Error('asynchronous renderer failure'))
    await firstStart

    expect(failures).toEqual([{
      kind: 'operation', message: 'asynchronous renderer failure',
    }])
    expect(port.locked).toBe(true)
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    const retry = lifecycle.start(async () => world)
    port.acquire()
    await retry

    expect(openCalls).toBe(2)
    expect(failures).toHaveLength(1)
  })

  it('keeps a cancelled Promise grant isolated until asynchronous unlock', async () => {
    const port = new TestPointerLockPort()
    const oldRequest = deferred<void>()
    port.requestResult = oldRequest.promise
    const gate = new PointerLockGate(port)

    const cancelled = gate.acquire()
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    cancelled.cancel()
    await expect(cancelled.result).rejects.toThrow('cancelled')

    port.acquire()
    oldRequest.resolve()
    await oldRequest.promise
    await Promise.resolve()

    expect(port.locked).toBe(true)
    expect(port.releases).toBeGreaterThan(0)
    const refusedWhileUnlocking = gate.acquire()
    expect(port.timeline).toEqual(['request'])
    await expect(refusedWhileUnlocking.result).rejects.toThrow('still settling')

    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    const freshRequest = deferred<void>()
    port.requestResult = freshRequest.promise
    const fresh = gate.acquire()
    expect(port.timeline).toEqual(['request', 'request'])
    port.acquire()
    freshRequest.resolve()
    await fresh.result

    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('keeps a cancelled legacy grant isolated until asynchronous unlock', async () => {
    const port = new TestPointerLockPort()
    const gate = new PointerLockGate(port)

    const cancelled = gate.acquire()
    cancelled.cancel()
    await expect(cancelled.result).rejects.toThrow('cancelled')

    port.acquire()
    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    const refusedWhileUnlocking = gate.acquire()
    expect(port.timeline).toEqual(['request'])
    await expect(refusedWhileUnlocking.result).rejects.toThrow('still settling')

    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    const fresh = gate.acquire()
    expect(port.timeline).toEqual(['request', 'request'])
    port.acquire()
    await fresh.result

    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('does not let a released lock satisfy a retry before asynchronous unlock', async () => {
    const port = new TestPointerLockPort()
    const gate = new PointerLockGate(port)
    const first = gate.acquire()
    port.acquire()
    await first.result

    gate.release()
    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    expect(port.changeListenerCount).toBe(1)
    const refusedWhileUnlocking = gate.acquire()
    expect(port.timeline).toEqual(['request'])
    await expect(refusedWhileUnlocking.result).rejects.toThrow('still settling')

    port.unlock()
    const retry = gate.acquire()
    expect(port.timeline).toEqual(['request', 'request'])
    port.acquire()
    await retry.result
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('cleans an idle gate after request throw and a cancelled denial', async () => {
    const port = new TestPointerLockPort()
    const gate = new PointerLockGate(port)
    port.requestError = new Error('request exploded')

    await expect(gate.acquire().result).rejects.toThrow('request exploded')
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)

    port.requestError = null
    const cancelled = gate.acquire()
    cancelled.cancel()
    await expect(cancelled.result).rejects.toThrow('cancelled')
    port.fail(new Error('late denial'))

    expect(port.locked).toBe(false)
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('preserves a cancelled drain when release throws until unlock is observed', async () => {
    const port = new TestPointerLockPort()
    const gate = new PointerLockGate(port)
    port.releaseError = new Error('release exploded')
    const cancelled = gate.acquire()
    cancelled.cancel()
    await expect(cancelled.result).rejects.toThrow('cancelled')

    expect(() => port.acquire()).not.toThrow()
    expect(port.locked).toBe(true)
    expect(port.releases).toBe(1)
    await expect(gate.acquire().result).rejects.toThrow('still settling')
    expect(port.timeline).toEqual(['request'])

    port.releaseError = null
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('finishes a cancelled Promise drain on asynchronous denial', async () => {
    const port = new TestPointerLockPort()
    const request = deferred<void>()
    port.requestResult = request.promise
    const gate = new PointerLockGate(port)
    const cancelled = gate.acquire()
    cancelled.cancel()
    await expect(cancelled.result).rejects.toThrow('cancelled')

    request.reject(new Error('late denial'))
    await expect(request.promise).rejects.toThrow('late denial')
    await until(() => port.changeListenerCount === 0)

    expect(port.locked).toBe(false)
    expect(port.errorListenerCount).toBe(0)
    port.requestResult = undefined
    const fresh = gate.acquire()
    expect(port.timeline).toEqual(['request', 'request'])
    port.acquire()
    await fresh.result
  })

  it('cancels a Promise-backed acquisition and releases a late grant after disposal', async () => {
    const port = new TestPointerLockPort()
    const requested = deferred<void>()
    port.requestResult = requested.promise
    const lifecycle = lifecycleWith(port, [], [])
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
    let operationCalls = 0
    let startSettled = false

    const starting = lifecycle.start(async () => {
      operationCalls++
      return world
    }).finally(() => { startSettled = true })
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    lifecycle.dispose()
    await until(() => startSettled)

    expect(operationCalls).toBe(0)
    expect(port.releases).toBe(1)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)

    port.acquire()
    requested.resolve()
    await starting

    expect(port.locked).toBe(true)
    expect(port.releases).toBe(2)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('settles a cancelled legacy acquisition and rejects a late lock without listener growth', async () => {
    const port = new TestPointerLockPort()
    const lifecycle = lifecycleWith(port, [], [])
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
    let operationCalls = 0
    let startSettled = false

    const starting = lifecycle.start(async () => {
      operationCalls++
      return world
    }).finally(() => { startSettled = true })
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    lifecycle.dispose()
    await until(() => startSettled)

    expect(operationCalls).toBe(0)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)

    port.acquire()
    port.fail(new Error('late denial'))
    await starting

    expect(port.locked).toBe(true)
    expect(port.releases).toBe(2)
    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.unlock()
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('cancels a Promise-backed resume acquisition before gate teardown', async () => {
    const port = new TestPointerLockPort()
    const requested = deferred<void>()
    port.requestResult = requested.promise
    const gate = new PointerLockGate(port)
    const resumePointerLock = new ResumePointerLock(gate)

    const resuming = resumePointerLock.request()
    resumePointerLock.dispose()
    gate.dispose()
    await expect(resuming).rejects.toThrow('cancelled')

    expect(port.changeListenerCount).toBe(1)
    expect(port.errorListenerCount).toBe(1)
    port.acquire()
    requested.resolve()
    await requested.promise
    await Promise.resolve()

    expect(port.locked).toBe(true)
    expect(port.changeListenerCount).toBe(1)
    port.unlock()
    await until(() => port.changeListenerCount === 0)

    expect(port.locked).toBe(false)
    expect(port.errorListenerCount).toBe(0)
  })

  it('rejects a concurrent resume request before a second platform call', async () => {
    const port = new TestPointerLockPort()
    const gate = new PointerLockGate(port)
    const resumePointerLock = new ResumePointerLock(gate)

    const first = resumePointerLock.request()
    const overlapping = resumePointerLock.request()
    expect(port.timeline).toEqual(['request'])
    await expect(overlapping).rejects.toThrow('already in progress')

    port.acquire()
    await first
    expect(port.changeListenerCount).toBe(0)
    expect(port.errorListenerCount).toBe(0)
  })

  it('cancels a legacy resume acquisition and cleans listeners after a late grant', async () => {
    const grantedPort = new TestPointerLockPort()
    const grantedGate = new PointerLockGate(grantedPort)
    const grantedResume = new ResumePointerLock(grantedGate)
    const granting = grantedResume.request()

    grantedResume.dispose()
    grantedGate.dispose()
    await expect(granting).rejects.toThrow('cancelled')
    grantedPort.acquire()

    expect(grantedPort.locked).toBe(true)
    expect(grantedPort.changeListenerCount).toBe(1)
    expect(grantedPort.errorListenerCount).toBe(1)
    grantedPort.unlock()

    expect(grantedPort.locked).toBe(false)
    expect(grantedPort.changeListenerCount).toBe(0)
    expect(grantedPort.errorListenerCount).toBe(0)
  })

  it('cancels a legacy resume acquisition and cleans listeners after a late error', async () => {
    const deniedPort = new TestPointerLockPort()
    const deniedGate = new PointerLockGate(deniedPort)
    const deniedResume = new ResumePointerLock(deniedGate)
    const denying = deniedResume.request()

    deniedResume.dispose()
    deniedGate.dispose()
    await expect(denying).rejects.toThrow('cancelled')
    deniedPort.fail(new Error('late denial'))

    expect(deniedPort.locked).toBe(false)
    expect(deniedPort.changeListenerCount).toBe(0)
    expect(deniedPort.errorListenerCount).toBe(0)
  })
})
