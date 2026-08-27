export type CursorPosition = { readonly x: number; readonly y: number }

export type DesktopMousePort = {
  setCaptured(captured: boolean): Promise<void>
  setCursorVisible(visible: boolean): Promise<void>
  setCursorPosition(position: CursorPosition): Promise<void>
}

export class DesktopMouse {
  private active = false
  private synchronizing = false
  private refreshRequested = false
  private refreshInFlight: Promise<void> | null = null
  private programmedPosition: CursorPosition | null = null
  private observedScreenPosition: CursorPosition | null = null
  private acknowledgeCenter: (() => void) | null = null
  private readonly onMouseMove = (event: MouseEvent): void => {
    const center = this.center()
    const position = { x: event.clientX, y: event.clientY }
    const screenPosition = Number.isFinite(event.screenX) && Number.isFinite(event.screenY)
      ? { x: event.screenX, y: event.screenY }
      : null
    if (this.samePosition(position, center)) {
      this.programmedPosition = center
      this.observedScreenPosition = screenPosition
      this.acknowledgeCenter?.()
      return
    }
    if (
      screenPosition !== null
      && this.observedScreenPosition !== null
      && this.samePosition(screenPosition, this.observedScreenPosition)
    ) {
      this.programCursorPosition(center)
      return
    }
    if (this.programmedPosition !== null && this.samePosition(position, this.programmedPosition)) {
      this.programCursorPosition(center)
      return
    }
    if (!this.active) {
      return
    }
    if (this.synchronizing) return
    const reference = this.programmedPosition ?? center
    const delta = screenPosition !== null && this.observedScreenPosition !== null
      ? {
          x: screenPosition.x - this.observedScreenPosition.x,
          y: screenPosition.y - this.observedScreenPosition.y,
        }
      : { x: position.x - reference.x, y: position.y - reference.y }
    this.observedScreenPosition = screenPosition
    this.onRelativeMotion(delta)
    this.programCursorPosition(center)
  }

  public constructor(
    private readonly canvas: HTMLCanvasElement,
    private readonly port: DesktopMousePort,
    private readonly onRelativeMotion: (delta: CursorPosition) => void,
  ) {}

  public async capture(): Promise<void> {
    if (this.active) return
    const centered = new Promise<void>((resolve) => {
      const timeout = setTimeout(resolve, 250)
      this.acknowledgeCenter = () => {
        clearTimeout(timeout)
        resolve()
      }
    })
    try {
      this.canvas.addEventListener('mousemove', this.onMouseMove)
      await this.port.setCaptured(true)
      await this.port.setCursorVisible(false)
      const center = this.center()
      this.programmedPosition = center
      await this.port.setCursorPosition(center)
      await centered
      this.acknowledgeCenter = null
      this.active = true
    } catch (error) {
      this.acknowledgeCenter = null
      this.refreshRequested = false
      this.programmedPosition = null
      this.observedScreenPosition = null
      this.canvas.removeEventListener('mousemove', this.onMouseMove)
      await this.restoreFreeCursor()
      throw error
    }
  }

  public async release(): Promise<void> {
    if (!this.active) return
    try {
      await this.port.setCaptured(false)
      await this.port.setCursorVisible(true)
    } catch (error) {
      await this.port.setCaptured(true).catch(() => {})
      await this.port.setCursorVisible(false).catch(() => {})
      throw error
    }
    this.active = false
    this.acknowledgeCenter = null
    this.refreshRequested = false
    this.programmedPosition = null
    this.observedScreenPosition = null
    this.canvas.removeEventListener('mousemove', this.onMouseMove)
  }

  public refreshCapture(): Promise<void> {
    if (!this.active) return Promise.resolve()
    this.refreshRequested = true
    if (this.refreshInFlight !== null) return this.refreshInFlight
    const refresh = this.runCaptureRefreshes().finally(() => {
      if (this.refreshInFlight === refresh) this.refreshInFlight = null
    })
    this.refreshInFlight = refresh
    return refresh
  }

  private center(): CursorPosition {
    const bounds = this.canvas.getBoundingClientRect()
    return { x: bounds.left + bounds.width / 2, y: bounds.top + bounds.height / 2 }
  }

  private samePosition(left: CursorPosition, right: CursorPosition): boolean {
    return Math.abs(left.x - right.x) < 1 && Math.abs(left.y - right.y) < 1
  }

  private async refreshCaptureNow(): Promise<void> {
    this.synchronizing = true
    const centered = new Promise<void>((resolve) => {
      const timeout = setTimeout(resolve, 250)
      this.acknowledgeCenter = () => {
        clearTimeout(timeout)
        resolve()
      }
    })
    try {
      await this.port.setCaptured(true)
      const center = this.center()
      this.programmedPosition = center
      await this.port.setCursorPosition(center)
      await centered
      this.acknowledgeCenter = null
    } finally {
      this.acknowledgeCenter = null
      this.synchronizing = false
    }
  }

  private async runCaptureRefreshes(): Promise<void> {
    while (this.active && this.refreshRequested) {
      this.refreshRequested = false
      await this.refreshCaptureNow()
    }
  }

  private programCursorPosition(position: CursorPosition): void {
    this.programmedPosition = position
    void this.port.setCursorPosition(position).catch(() => {})
  }

  private async restoreFreeCursor(): Promise<void> {
    try {
      await this.port.setCaptured(false)
    } finally {
      await this.port.setCursorVisible(true)
    }
  }
}
