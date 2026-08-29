import type { GameWorld } from './model'

export type StartFailure = { readonly kind: 'operation'; readonly message: string }
export type StartControl = { disabled: boolean }

type StartLifecycleHooks = {
  readonly open: (world: GameWorld) => void | Promise<void>
  readonly fail: (failure: StartFailure) => void
}

type StartPhase = 'idle' | 'starting' | 'started' | 'disposed'

function failureMessage(error: unknown): string {
  if (error instanceof Error && error.message.length > 0) return error.message
  if (typeof error === 'string' && error.length > 0) return error
  return 'start operation failed'
}

export class StartLifecycle {
  private phase: StartPhase = 'idle'
  private generation = 0
  private readonly controls = new Set<StartControl>()

  public constructor(private readonly hooks: StartLifecycleHooks) {}

  public get busy(): boolean { return this.phase === 'starting' }

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
    return this.finishStart(generation, operation)
  }

  public returnToMenu(): void {
    if (this.phase !== 'started') throw new Error('only a started world can return to the menu')
    this.phase = 'idle'
    this.generation++
    this.syncControls()
  }

  public dispose(): void {
    if (this.phase === 'disposed') return
    this.phase = 'disposed'
    this.generation++
    this.syncControls()
    this.controls.clear()
  }

  private async finishStart(generation: number, operation: () => Promise<GameWorld>): Promise<void> {
    try {
      const world = await operation()
      if (!this.isCurrent(generation)) return
      await this.hooks.open(world)
      if (!this.isCurrent(generation)) return
      this.phase = 'started'
      this.syncControls()
    } catch (error) {
      if (!this.isCurrent(generation)) return
      this.phase = 'idle'
      this.syncControls()
      this.hooks.fail({ kind: 'operation', message: failureMessage(error) })
    }
  }

  private isCurrent(generation: number): boolean {
    return this.phase === 'starting' && this.generation === generation
  }

  private syncControls(): void {
    for (const control of this.controls) control.disabled = this.busy
  }
}
