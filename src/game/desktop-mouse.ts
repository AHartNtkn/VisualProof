export type CursorPosition = { readonly x: number; readonly y: number }

export type DesktopMousePort = {
  setCaptured(captured: boolean): Promise<void>
  setCursorVisible(visible: boolean): Promise<void>
  setCursorPosition(position: CursorPosition): Promise<void>
}

export class DesktopMouse {
  private active = false
  private readonly onMouseMove = (event: MouseEvent): void => {
    if (!this.active) return
    const center = this.center()
    const delta = { x: event.clientX - center.x, y: event.clientY - center.y }
    if (delta.x === 0 && delta.y === 0) return
    this.onRelativeMotion(delta)
    void this.port.setCursorPosition(center).catch(() => {})
  }

  public constructor(
    private readonly canvas: HTMLCanvasElement,
    private readonly port: DesktopMousePort,
    private readonly onRelativeMotion: (delta: CursorPosition) => void,
  ) {}

  public async capture(): Promise<void> {
    if (this.active) return
    try {
      await this.port.setCaptured(true)
      await this.port.setCursorVisible(false)
      await this.port.setCursorPosition(this.center())
      this.canvas.addEventListener('mousemove', this.onMouseMove)
      this.active = true
    } catch (error) {
      await this.restoreFreeCursor()
      throw error
    }
  }

  public async release(): Promise<void> {
    if (!this.active) return
    this.active = false
    this.canvas.removeEventListener('mousemove', this.onMouseMove)
    await this.restoreFreeCursor()
  }

  private center(): CursorPosition {
    const bounds = this.canvas.getBoundingClientRect()
    return { x: bounds.left + bounds.width / 2, y: bounds.top + bounds.height / 2 }
  }

  private async restoreFreeCursor(): Promise<void> {
    try {
      await this.port.setCaptured(false)
    } finally {
      await this.port.setCursorVisible(true)
    }
  }
}
