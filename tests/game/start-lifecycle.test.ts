import { describe, expect, it } from 'vitest'
import type { GameWorld } from '../../src/game/model'
import { StartLifecycle, type StartFailure } from '../../src/game/start-lifecycle'

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

describe('game start lifecycle', () => {
  it('loads with a free menu and opens only after its decoded world succeeds', async () => {
    const loading = deferred<GameWorld>()
    const opened: GameWorld[] = []
    const lifecycle = new StartLifecycle({ open: (loaded) => { opened.push(loaded) }, fail: () => {} })
    const menuControl = { disabled: false }
    lifecycle.registerControl(menuControl)
    let loadingStarted = false

    const starting = lifecycle.start(async () => {
      loadingStarted = true
      return loading.promise
    })
    await until(() => loadingStarted)

    expect(opened).toEqual([])
    expect(menuControl.disabled).toBe(true)
    loading.resolve(world)
    await starting

    expect(opened).toEqual([world])
    expect(menuControl.disabled).toBe(false)
  })

  it('returns an opening failure to the menu and permits a later load', async () => {
    const failures: StartFailure[] = []
    const control = { disabled: false }
    let attempts = 0
    const lifecycle = new StartLifecycle({
      open: () => {
        attempts++
        if (attempts === 1) throw new Error('renderer initialization failed')
      },
      fail: (failure) => failures.push(failure),
    })
    lifecycle.registerControl(control)

    await lifecycle.start(async () => world)
    expect(failures).toEqual([{ kind: 'operation', message: 'renderer initialization failed' }])
    expect(control.disabled).toBe(false)

    await lifecycle.start(async () => world)
    expect(attempts).toBe(2)
  })

  it('does not open a late load after disposal', async () => {
    const loading = deferred<GameWorld>()
    const opened: GameWorld[] = []
    const lifecycle = new StartLifecycle({ open: (loaded) => { opened.push(loaded) }, fail: () => {} })
    let loadingStarted = false
    const starting = lifecycle.start(async () => {
      loadingStarted = true
      return loading.promise
    })
    await until(() => loadingStarted)

    lifecycle.dispose()
    loading.resolve(world)
    await starting

    expect(opened).toEqual([])
  })
})
