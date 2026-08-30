import { exitOrbit, type CameraState } from '../src/game/camera'
import type { ToolInventory } from '../src/game/tools'
import type { WorldInput } from './input'

type LedgerStatePort = {
  readonly isOpen: boolean
}

type PauseMenuPort = {
  show(worldName: string): void
  hide(): void
}

export type WorldStatePorts = {
  readonly getCamera: () => CameraState
  readonly setCamera: (camera: CameraState) => void
  readonly tools: ToolInventory
  readonly ledger: LedgerStatePort
  readonly input: Pick<WorldInput, 'suspend' | 'resume' | 'engage'>
  readonly pauseMenu: PauseMenuPort
  readonly worldName: () => string
  readonly setFreeActive: (active: boolean) => void
  readonly cuttingCleared: () => void
  readonly stateChanged: () => void
}

export class WorldStateController {
  #paused = false

  public constructor(private readonly ports: WorldStatePorts) {}

  public get isPaused(): boolean {
    return this.#paused
  }

  public pause(): boolean {
    if (this.#paused) return false
    this.#paused = true
    this.ports.setFreeActive(false)
    this.ports.input.suspend()
    this.ports.pauseMenu.show(this.ports.worldName())
    this.ports.stateChanged()
    return true
  }

  public resume(): boolean {
    if (!this.#paused) return false
    this.ports.pauseMenu.hide()
    this.#paused = false
    if (!this.ports.ledger.isOpen) {
      this.ports.input.resume()
      if (this.ports.getCamera().mode === 'free') this.engageFreeFlight()
    }
    this.ports.stateChanged()
    return true
  }

  public stepBack(): 'cutting-cleared' | 'orbit-exited' | 'unchanged' {
    if (this.#paused || this.ports.ledger.isOpen) return 'unchanged'
    if (this.ports.tools.cutting !== null) {
      this.ports.tools.cancel()
      this.ports.cuttingCleared()
      this.ports.stateChanged()
      return 'cutting-cleared'
    }
    const camera = this.ports.getCamera()
    if (camera.mode !== 'orbit') return 'unchanged'
    this.ports.setCamera(exitOrbit(camera))
    this.ports.setFreeActive(false)
    this.engageFreeFlight()
    this.ports.stateChanged()
    return 'orbit-exited'
  }

  private engageFreeFlight(): void {
    void this.ports.input.engage().catch(() => {
      this.ports.setFreeActive(false)
      this.ports.stateChanged()
    })
  }
}
