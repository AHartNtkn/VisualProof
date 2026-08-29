import type { CameraMotion } from '../src/game/camera'

export type WorldInputActions = {
  readonly pointerDown: (button: number, clientX: number, clientY: number) => void
  readonly pointerUp: (button: number, clientX: number, clientY: number) => void
  readonly pointerCancel: () => void
  readonly escape: () => boolean
  readonly swapTool: () => void
  readonly toggleCatalog: () => void
  readonly engagementChanged: (active: boolean) => void
}

export type WorldInput = {
  sample(): CameraMotion
  engage(): Promise<void>
  release(): void
  dispose(): void
}

export function requestWorldEngagement(target: HTMLElement): Promise<void> {
  try {
    return Promise.resolve(target.requestPointerLock())
  } catch (error) {
    return Promise.reject(error)
  }
}

export function attachWorldInput(
  target: HTMLElement,
  actions: WorldInputActions,
  environment: { readonly window: Window; readonly document: Document } = { window, document },
): WorldInput {
  const held = new Set<string>()
  const disposers: Array<() => void> = []
  let lookX = 0
  let lookY = 0
  let gestureActive = false

  const clear = (): void => {
    held.clear()
    lookX = 0
    lookY = 0
  }
  const abortPointer = (): void => {
    if (!gestureActive) return
    gestureActive = false
    actions.pointerCancel()
  }
  const listen = (eventTarget: EventTarget, type: string, listener: EventListener): void => {
    eventTarget.addEventListener(type, listener)
    disposers.push(() => eventTarget.removeEventListener(type, listener))
  }
  const down = ((event: KeyboardEvent): void => {
    if (event.code === 'Digit1' || event.code === 'Tab') {
      event.preventDefault()
      if (event.repeat) return
      if (event.code === 'Digit1') actions.swapTool()
      else actions.toggleCatalog()
      return
    }
    if (event.code === 'Escape') {
      if (!actions.escape()) return
      event.preventDefault()
      clear()
      void requestWorldEngagement(target).catch(() => actions.engagementChanged(false))
      return
    }
    held.add(event.code)
  }) as EventListener
  const up = ((event: KeyboardEvent): void => { held.delete(event.code) }) as EventListener
  const mouseMove = ((event: MouseEvent): void => {
    if (environment.document.pointerLockElement === target) {
      lookX += event.movementX
      lookY += event.movementY
    }
  }) as EventListener
  const mouseDown = ((event: MouseEvent): void => {
    gestureActive = true
    actions.pointerDown(event.button, event.clientX, event.clientY)
  }) as EventListener
  const mouseUp = ((event: MouseEvent): void => {
    if (!gestureActive) return
    gestureActive = false
    actions.pointerUp(event.button, event.clientX, event.clientY)
  }) as EventListener
  const wheel = ((event: WheelEvent): void => {
    event.preventDefault()
  }) as EventListener
  const contextMenu = ((event: Event): void => { event.preventDefault() }) as EventListener
  const pointerLockChange = (): void => {
    const active = environment.document.pointerLockElement === target
    if (!active) {
      abortPointer()
      clear()
    }
    actions.engagementChanged(active)
  }
  const visibilityChange = (): void => {
    if (environment.document.visibilityState === 'hidden') {
      abortPointer()
      clear()
      actions.engagementChanged(false)
    }
  }
  const blur = (): void => {
    abortPointer()
    clear()
    actions.engagementChanged(false)
  }

  listen(environment.window, 'keydown', down)
  listen(environment.window, 'keyup', up)
  listen(environment.window, 'mousemove', mouseMove)
  listen(target, 'mousedown', mouseDown)
  listen(environment.window, 'mouseup', mouseUp)
  listen(target, 'wheel', wheel)
  listen(target, 'contextmenu', contextMenu)
  listen(environment.document, 'pointerlockchange', pointerLockChange)
  listen(environment.window, 'blur', blur)
  listen(environment.document, 'visibilitychange', visibilityChange)
  actions.engagementChanged(environment.document.pointerLockElement === target)

  return {
    sample: () => {
      const sample = {
        forward: Number(held.has('KeyW')) - Number(held.has('KeyS')),
        strafe: Number(held.has('KeyD')) - Number(held.has('KeyA')),
        vertical: Number(held.has('Space'))
          - Number(held.has('ControlLeft') || held.has('ControlRight')),
        sprint: held.has('ShiftLeft') || held.has('ShiftRight'),
        lookX,
        lookY,
      }
      lookX = 0
      lookY = 0
      return sample
    },
    engage: () => requestWorldEngagement(target),
    release: () => {
      if (environment.document.pointerLockElement === target) environment.document.exitPointerLock()
    },
    dispose: () => {
      abortPointer()
      clear()
      for (const dispose of disposers.splice(0)) dispose()
    },
  }
}
