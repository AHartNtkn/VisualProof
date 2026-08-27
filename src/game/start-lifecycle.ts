import type { GameWorld } from './model'

export type PointerLockPort = {
  request(): void | Promise<void>
  isLocked(): boolean
  onChange(listener: () => void): () => void
  onError(listener: (error?: unknown) => void): () => void
  release(): void
}

export type StartFailure = {
  readonly kind: 'pointer-lock' | 'operation'
  readonly message: string
}

export type StartControl = { disabled: boolean }

type StartLifecycleHooks = {
  readonly open: (world: GameWorld) => void
  readonly fail: (failure: StartFailure) => void
}

function failureMessage(error: unknown, fallback: string): string {
  if (error instanceof Error && error.message.length > 0) return error.message
  if (typeof error === 'string' && error.length > 0) return error
  return fallback
}

function promiseLike(value: unknown): value is PromiseLike<void> {
  return (typeof value === 'object' && value !== null || typeof value === 'function')
    && 'then' in value
    && typeof (value as { readonly then?: unknown }).then === 'function'
}

export class PointerLockGate {
  public constructor(private readonly port: PointerLockPort) {}

  public acquire(): Promise<void> {
    return new Promise((resolve, reject) => {
      let settled = false
      let removeChange = (): void => {}
      let removeError = (): void => {}
      const cleanup = (): void => {
        removeChange()
        removeError()
      }
      const succeed = (): void => {
        if (settled || !this.port.isLocked()) return
        settled = true
        cleanup()
        resolve()
      }
      const fail = (error?: unknown): void => {
        if (settled) return
        settled = true
        cleanup()
        reject(new Error(failureMessage(error, 'pointer lock was denied')))
      }
      removeChange = this.port.onChange(succeed)
      removeError = this.port.onError(fail)

      let request: void | Promise<void>
      try {
        request = this.port.request()
      } catch (error) {
        fail(error)
        return
      }
      succeed()
      if (promiseLike(request)) {
        void Promise.resolve(request).then(succeed, fail)
      }
    })
  }

  public release(): void {
    this.port.release()
  }
}

type StartPhase = 'idle' | 'starting' | 'started' | 'disposed'

export class StartLifecycle {
  private phase: StartPhase = 'idle'
  private generation = 0
  private readonly controls = new Set<StartControl>()

  public constructor(
    private readonly pointerLock: PointerLockGate,
    private readonly hooks: StartLifecycleHooks,
  ) {}

  public get busy(): boolean {
    return this.phase === 'starting'
  }

  public registerControl(control: StartControl): () => void {
    this.controls.add(control)
    control.disabled = this.busy
    return () => this.controls.delete(control)
  }

  public start(operation: () => Promise<GameWorld>): Promise<void> {
    if (this.phase !== 'idle') return Promise.resolve()
    this.phase = 'starting'
    const generation = ++this.generation
    this.syncControls()
    const acquisition = this.pointerLock.acquire()
    return this.finishStart(generation, acquisition, operation)
  }

  public dispose(): void {
    if (this.phase === 'disposed') return
    this.phase = 'disposed'
    this.generation++
    this.syncControls()
    this.pointerLock.release()
    this.controls.clear()
  }

  private async finishStart(
    generation: number,
    acquisition: Promise<void>,
    operation: () => Promise<GameWorld>,
  ): Promise<void> {
    let acquired = false
    try {
      await acquisition
      acquired = true
      if (!this.isCurrent(generation)) return
      const world = await operation()
      if (!this.isCurrent(generation)) return
      this.phase = 'started'
      this.syncControls()
      this.hooks.open(world)
    } catch (error) {
      if (!this.isCurrent(generation)) return
      this.pointerLock.release()
      this.phase = 'idle'
      this.syncControls()
      this.hooks.fail({
        kind: acquired ? 'operation' : 'pointer-lock',
        message: failureMessage(error, acquired ? 'start operation failed' : 'pointer lock was denied'),
      })
    }
  }

  private isCurrent(generation: number): boolean {
    return this.phase === 'starting' && this.generation === generation
  }

  private syncControls(): void {
    for (const control of this.controls) control.disabled = this.busy
  }
}
