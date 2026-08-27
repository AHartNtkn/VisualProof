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

type PointerLockAttempt = {
  readonly resolve: () => void
  readonly reject: (error: Error) => void
  requestKind: 'legacy' | 'promise'
}

type DrainingPointerLockAttempt = {
  readonly attempt: PointerLockAttempt
  readonly requestKind: 'legacy' | 'promise'
}

type StartLifecycleHooks = {
  readonly open: (world: GameWorld) => void | Promise<void>
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
  private active: PointerLockAttempt | null = null
  private draining: DrainingPointerLockAttempt | null = null
  private disposed = false
  private removeChange: () => void
  private removeError: () => void

  public constructor(private readonly port: PointerLockPort) {
    // These are gate-lifetime listeners, not acquisition-lifetime listeners. Keeping
    // one bounded watcher lets a cancelled legacy request reject a late native grant
    // without leaving its acquisition Promise or callbacks pending.
    this.removeChange = this.port.onChange(() => this.handleChange())
    this.removeError = this.port.onError((error) => this.handleError(error))
  }

  public acquire(): PointerLockAcquisition {
    if (this.disposed) {
      return {
        result: Promise.reject(new Error('pointer lock gate is disposed')),
        cancel: () => {},
      }
    }
    if (this.draining !== null) {
      return {
        result: Promise.reject(new Error('previous pointer lock request is still settling')),
        cancel: () => {},
      }
    }
    if (this.active !== null) {
      return {
        result: Promise.reject(new Error('pointer lock acquisition is already in progress')),
        cancel: () => {},
      }
    }

    let attempt!: PointerLockAttempt
    const result = new Promise<void>((resolve, reject) => {
      attempt = { resolve, reject, requestKind: 'legacy' }
      this.active = attempt
    })
    const cancel = (): void => this.cancel(attempt)

    let request: void | Promise<void>
    try {
      request = this.port.request()
    } catch (error) {
      this.fail(attempt, error)
      return { result, cancel }
    }
    attempt.requestKind = promiseLike(request) ? 'promise' : 'legacy'
    this.succeed(attempt)
    if (promiseLike(request)) {
      void Promise.resolve(request).then(
        () => this.finishPromiseRequest(attempt, true),
        (error) => this.finishPromiseRequest(attempt, false, error),
      )
    }
    return { result, cancel }
  }

  public release(): void {
    this.port.release()
  }

  public dispose(): void {
    if (this.disposed) return
    this.disposed = true
    if (this.active !== null) this.cancel(this.active)
    this.port.release()
    this.cleanupListeners()
  }

  private handleChange(): void {
    const draining = this.draining
    if (draining !== null) {
      if (draining.requestKind === 'legacy') this.finishDrain(draining.attempt)
      if (this.port.isLocked()) this.port.release()
      return
    }
    if (!this.port.isLocked()) return
    if (this.active !== null) {
      this.succeed(this.active)
    }
  }

  private handleError(error?: unknown): void {
    const draining = this.draining
    if (draining !== null) {
      if (draining.requestKind === 'legacy') this.finishDrain(draining.attempt)
      return
    }
    if (this.active !== null) this.fail(this.active, error)
  }

  private finishPromiseRequest(
    attempt: PointerLockAttempt,
    succeeded: boolean,
    error?: unknown,
  ): void {
    if (this.active === attempt) {
      if (succeeded) this.succeed(attempt)
      else this.fail(attempt, error)
      return
    }
    if (this.draining?.attempt !== attempt) return
    this.finishDrain(attempt)
    if (this.port.isLocked()) this.port.release()
  }

  private cancel(attempt: PointerLockAttempt): void {
    if (this.active !== attempt) return
    this.active = null
    this.draining = { attempt, requestKind: attempt.requestKind }
    attempt.reject(new Error('pointer lock acquisition was cancelled'))
  }

  private finishDrain(attempt: PointerLockAttempt): void {
    if (this.draining?.attempt !== attempt) return
    this.draining = null
    this.cleanupListeners()
  }

  private cleanupListeners(): void {
    if (!this.disposed || this.active !== null || this.draining !== null) return
    this.removeChange()
    this.removeError()
    this.removeChange = () => {}
    this.removeError = () => {}
  }

  private succeed(attempt: PointerLockAttempt): void {
    if (this.active !== attempt || !this.port.isLocked()) return
    this.active = null
    attempt.resolve()
  }

  private fail(attempt: PointerLockAttempt, error?: unknown): void {
    if (this.active !== attempt) return
    this.active = null
    attempt.reject(new Error(failureMessage(error, 'pointer lock was denied')))
  }
}

export type PointerLockAcquisition = {
  readonly result: Promise<void>
  cancel(): void
}

export class ResumePointerLock {
  private acquisition: PointerLockAcquisition | null = null
  private disposed = false

  public constructor(private readonly pointerLock: PointerLockGate) {}

  public request(): Promise<void> {
    if (this.disposed) return Promise.reject(new Error('resume pointer lock is disposed'))
    if (this.acquisition !== null) {
      return Promise.reject(new Error('resume pointer lock request is already in progress'))
    }
    const acquisition = this.pointerLock.acquire()
    this.acquisition = acquisition
    return acquisition.result.finally(() => {
      if (this.acquisition === acquisition) this.acquisition = null
    })
  }

  public dispose(): void {
    if (this.disposed) return
    this.disposed = true
    this.acquisition?.cancel()
    this.acquisition = null
    this.pointerLock.release()
  }
}

type StartPhase = 'idle' | 'starting' | 'started' | 'disposed'

export class StartLifecycle {
  private phase: StartPhase = 'idle'
  private generation = 0
  private readonly controls = new Set<StartControl>()
  private acquisition: PointerLockAcquisition | null = null

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
    this.acquisition = acquisition
    return this.finishStart(generation, acquisition, operation)
  }

  public dispose(): void {
    if (this.phase === 'disposed') return
    this.phase = 'disposed'
    this.generation++
    this.syncControls()
    this.acquisition?.cancel()
    this.acquisition = null
    this.pointerLock.release()
    this.controls.clear()
  }

  private async finishStart(
    generation: number,
    acquisition: PointerLockAcquisition,
    operation: () => Promise<GameWorld>,
  ): Promise<void> {
    let acquired = false
    try {
      await acquisition.result
      acquired = true
      if (!this.isCurrent(generation)) return
      const world = await operation()
      if (!this.isCurrent(generation)) return
      await this.hooks.open(world)
      if (!this.isCurrent(generation)) return
      this.phase = 'started'
      this.syncControls()
    } catch (error) {
      if (!this.isCurrent(generation)) return
      this.pointerLock.release()
      this.phase = 'idle'
      this.syncControls()
      this.hooks.fail({
        kind: acquired ? 'operation' : 'pointer-lock',
        message: failureMessage(error, acquired ? 'start operation failed' : 'pointer lock was denied'),
      })
    } finally {
      if (this.acquisition === acquisition) this.acquisition = null
    }
  }

  private isCurrent(generation: number): boolean {
    return this.phase === 'starting' && this.generation === generation
  }

  private syncControls(): void {
    for (const control of this.controls) control.disabled = this.busy
  }
}
