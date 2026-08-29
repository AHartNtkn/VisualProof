import type { CameraPose } from './model'
import type { CameraRecord, PotPlacement, SaveClient, TreeUpdate } from './save-client'

export type SaveWriterStatus = {
  readonly state: 'idle' | 'saving' | 'error'
  readonly message?: string
}

export type SaveWriterClock = {
  setTimeout(run: () => void, milliseconds: number): unknown
  clearTimeout(id: unknown): void
}

type SaveWriterPort = Pick<
  SaveClient,
  | 'updateTree'
  | 'insertTree'
  | 'updateCamera'
  | 'acceptOrder'
  | 'abandonOrder'
  | 'completeOrder'
>

type PendingWrite =
  | { readonly kind: 'tree-insert'; readonly update: TreeUpdate }
  | { readonly kind: 'tree-update'; readonly update: TreeUpdate }
  | { readonly kind: 'camera'; readonly camera: CameraRecord }
  | { readonly kind: 'order-accept'; readonly orderId: string; readonly pot: PotPlacement }
  | { readonly kind: 'order-abandon'; readonly orderId: string }
  | { readonly kind: 'order-complete'; readonly orderId: string; readonly reward: number }

const CAMERA_DEBOUNCE_MS = 500

const systemClock: SaveWriterClock = {
  setTimeout: (run, milliseconds) => globalThis.setTimeout(run, milliseconds),
  clearTimeout: (id) => globalThis.clearTimeout(id as ReturnType<typeof setTimeout>),
}

function cameraRecord(pose: CameraPose): CameraRecord {
  return {
    x: pose.position.x,
    y: pose.position.y,
    z: pose.position.z,
    yaw: pose.yaw,
    pitch: pose.pitch,
  }
}

function replacementKey(write: PendingWrite): string | null {
  switch (write.kind) {
    case 'tree-update': return `tree-update:${write.update.treeId}`
    case 'camera': return 'camera'
    case 'tree-insert':
    case 'order-accept':
    case 'order-abandon':
    case 'order-complete': return null
  }
}

function errorMessage(error: unknown): string {
  return error instanceof Error ? error.message : String(error)
}

function sameCamera(left: CameraRecord | null, right: CameraRecord): boolean {
  return left !== null
    && left.x === right.x
    && left.y === right.y
    && left.z === right.z
    && left.yaw === right.yaw
    && left.pitch === right.pitch
}

export class SaveWriter {
  private readonly pending: PendingWrite[] = []
  private readonly listeners = new Set<(status: SaveWriterStatus) => void>()
  private status: SaveWriterStatus = { state: 'idle' }
  private activeDrain: Promise<void> | null = null
  private blocked = false
  private cameraTimer: unknown | null = null
  private newestCamera: CameraRecord | null = null
  private lastCamera: CameraRecord | null = null
  private closing = false
  private disposed = false
  private disposal: Promise<void> | null = null

  public constructor(
    private readonly slotId: string,
    private readonly port: SaveWriterPort,
    private readonly clock: SaveWriterClock = systemClock,
  ) {}

  public tree(update: TreeUpdate): void {
    this.assertAccepting()
    this.enqueue({ kind: 'tree-update', update })
  }

  public insertTree(update: TreeUpdate): void {
    this.assertAccepting()
    this.enqueue({ kind: 'tree-insert', update })
  }

  public acceptOrder(orderId: string, pot: PotPlacement): void {
    this.assertAccepting()
    this.enqueue({ kind: 'order-accept', orderId, pot })
  }

  public abandonOrder(orderId: string): void {
    this.assertAccepting()
    this.enqueue({ kind: 'order-abandon', orderId })
  }

  public completeOrder(orderId: string, reward: number): void {
    this.assertAccepting()
    this.enqueue({ kind: 'order-complete', orderId, reward })
  }

  public camera(camera: CameraPose): void {
    this.assertAccepting()
    const next = cameraRecord(camera)
    if (sameCamera(this.lastCamera, next)) return
    this.lastCamera = next
    this.newestCamera = next
    if (this.cameraTimer !== null) this.clock.clearTimeout(this.cameraTimer)
    this.cameraTimer = this.clock.setTimeout(() => {
      this.cameraTimer = null
      this.enqueueCamera()
    }, CAMERA_DEBOUNCE_MS)
  }

  public async flush(): Promise<void> {
    this.enqueueCamera()
    this.startDrain()
    while (this.activeDrain !== null) await this.activeDrain
  }

  public retry(): void {
    if (this.disposed || this.closing || !this.blocked) return
    this.blocked = false
    this.startDrain()
  }

  public subscribe(listener: (status: SaveWriterStatus) => void): () => void {
    this.listeners.add(listener)
    listener(this.status)
    return () => this.listeners.delete(listener)
  }

  public dispose(): Promise<void> {
    if (this.disposed) return Promise.resolve()
    if (this.disposal !== null) return this.disposal
    this.closing = true
    const disposal = this.finishDisposal()
    this.disposal = disposal
    const clear = (): void => {
      if (this.disposal === disposal) this.disposal = null
    }
    void disposal.then(clear, clear)
    return disposal
  }

  private async finishDisposal(): Promise<void> {
    this.enqueueCamera()
    this.blocked = false
    this.startDrain()
    while (this.activeDrain !== null) await this.activeDrain
    if (this.status.state === 'error') {
      this.closing = false
      throw new Error(this.status.message ?? 'save failed')
    }
    this.disposed = true
    this.closing = false
    this.listeners.clear()
  }

  private assertAccepting(): void {
    if (this.disposed || this.closing) throw new Error('save writer is disposed')
  }

  private enqueueCamera(): void {
    if (this.cameraTimer !== null) {
      this.clock.clearTimeout(this.cameraTimer)
      this.cameraTimer = null
    }
    const camera = this.newestCamera
    if (camera === null) return
    this.newestCamera = null
    this.enqueue({ kind: 'camera', camera })
  }

  private enqueue(write: PendingWrite): void {
    const key = replacementKey(write)
    if (key === null) this.pending.push(write)
    else {
      const existing = this.pending.findIndex((candidate) => replacementKey(candidate) === key)
      if (existing === -1) this.pending.push(write)
      else this.pending[existing] = write
    }
    if (this.blocked) this.blocked = false
    this.startDrain()
  }

  private startDrain(): void {
    if (this.activeDrain !== null || this.blocked || this.pending.length === 0) return
    this.publish({ state: 'saving' })
    this.activeDrain = this.drain().finally(() => {
      this.activeDrain = null
      if (!this.blocked && this.pending.length > 0) this.startDrain()
    })
  }

  private async drain(): Promise<void> {
    while (this.pending.length > 0) {
      const write = this.pending.shift()!
      try {
        switch (write.kind) {
          case 'tree-insert': await this.port.insertTree(this.slotId, write.update); break
          case 'tree-update': await this.port.updateTree(this.slotId, write.update); break
          case 'camera': await this.port.updateCamera(this.slotId, write.camera); break
          case 'order-accept': await this.port.acceptOrder(this.slotId, write.orderId, write.pot); break
          case 'order-abandon': await this.port.abandonOrder(this.slotId, write.orderId); break
          case 'order-complete': await this.port.completeOrder(this.slotId, write.orderId, write.reward); break
        }
      } catch (error) {
        this.pending.unshift(write)
        this.blocked = true
        this.publish({ state: 'error', message: errorMessage(error) })
        return
      }
    }
    this.publish({ state: 'idle' })
  }

  private publish(status: SaveWriterStatus): void {
    this.status = status
    for (const listener of this.listeners) listener(status)
  }
}
