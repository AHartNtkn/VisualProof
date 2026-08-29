import type { CameraMotion } from '../src/game/camera'

export type WorldInputActions = {
  readonly pointerDown: (button: number, clientX: number, clientY: number) => void
  readonly pointerMove: (clientX: number, clientY: number) => void
  readonly pointerUp: (button: number, clientX: number, clientY: number) => void
  readonly pointerCancel: () => void
  readonly wheel: (deltaY: number) => void
  readonly escape: () => boolean
  readonly engagementChanged: (active: boolean) => void
}

export type WorldInput = {
  sample(): CameraMotion
  engage(): Promise<void>
  release(): void
  dispose(): void
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
  let activePointerId: number | null = null

  const clear = (): void => {
    held.clear()
    lookX = 0
    lookY = 0
  }
  const abortPointer = (): void => {
    const pointerId = activePointerId
    if (pointerId === null) return
    activePointerId = null
    if (pointerId >= 0 && target.hasPointerCapture(pointerId)) {
      target.releasePointerCapture(pointerId)
    }
    actions.pointerCancel()
  }
  const requestEngagement = (): Promise<void> => {
    try {
      return Promise.resolve(target.requestPointerLock())
    } catch (error) {
      return Promise.reject(error)
    }
  }
  const listen = (eventTarget: EventTarget, type: string, listener: EventListener): void => {
    eventTarget.addEventListener(type, listener)
    disposers.push(() => eventTarget.removeEventListener(type, listener))
  }
  const down = ((event: KeyboardEvent): void => {
    if (event.code === 'Escape') {
      if (!actions.escape()) return
      event.preventDefault()
      clear()
      void requestEngagement().catch(() => actions.engagementChanged(false))
      return
    }
    held.add(event.code)
  }) as EventListener
  const up = ((event: KeyboardEvent): void => { held.delete(event.code) }) as EventListener
  const move = ((event: MouseEvent): void => {
    if (activePointerId !== null) actions.pointerMove(event.clientX, event.clientY)
    if (environment.document.pointerLockElement === target) {
      lookX += event.movementX
      lookY += event.movementY
    }
  }) as EventListener
  const pointerDown = ((event: PointerEvent): void => {
    activePointerId = event.pointerId
    target.setPointerCapture(event.pointerId)
  }) as EventListener
  const mouseDown = ((event: MouseEvent): void => {
    if (activePointerId === null) activePointerId = -1
    actions.pointerDown(event.button, event.clientX, event.clientY)
  }) as EventListener
  const mouseUp = ((event: MouseEvent): void => {
    if (activePointerId === null) return
    const pointerId = activePointerId
    activePointerId = null
    actions.pointerUp(event.button, event.clientX, event.clientY)
    if (pointerId >= 0 && target.hasPointerCapture(pointerId)) target.releasePointerCapture(pointerId)
  }) as EventListener
  const cancelPointer = ((event: PointerEvent): void => {
    if (event.pointerId !== activePointerId) return
    abortPointer()
  }) as EventListener
  const wheel = ((event: WheelEvent): void => {
    event.preventDefault()
    actions.wheel(event.deltaY)
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
  listen(target, 'mousemove', move)
  listen(target, 'pointerdown', pointerDown)
  listen(target, 'mousedown', mouseDown)
  listen(target, 'mouseup', mouseUp)
  listen(target, 'pointercancel', cancelPointer)
  listen(target, 'lostpointercapture', cancelPointer)
  listen(target, 'wheel', wheel)
  listen(target, 'contextmenu', contextMenu)
  listen(environment.document, 'pointerlockchange', pointerLockChange)
  listen(environment.window, 'blur', blur)
  listen(environment.document, 'visibilitychange', visibilityChange)

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
    engage: requestEngagement,
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
