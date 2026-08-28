import type { CameraMotion } from '../src/game/camera'

export type WorldInputActions = {
  readonly primary: (clientX: number, clientY: number) => void
  readonly escape: () => void
}

export type WorldInput = {
  sample(): CameraMotion
  clear(): void
  engaged(): boolean
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

  const clear = (): void => {
    held.clear()
    lookX = 0
    lookY = 0
  }
  const listen = (eventTarget: EventTarget, type: string, listener: EventListener): void => {
    eventTarget.addEventListener(type, listener)
    disposers.push(() => eventTarget.removeEventListener(type, listener))
  }
  const down = ((event: KeyboardEvent): void => {
    if (event.code === 'Escape') {
      actions.escape()
      return
    }
    held.add(event.code)
  }) as EventListener
  const up = ((event: KeyboardEvent): void => { held.delete(event.code) }) as EventListener
  const move = ((event: MouseEvent): void => {
    if (environment.document.pointerLockElement !== target) return
    lookX += event.movementX
    lookY += event.movementY
  }) as EventListener
  const primary = ((event: MouseEvent): void => {
    if (event.button === 0) actions.primary(event.clientX, event.clientY)
  }) as EventListener
  const contextMenu = ((event: Event): void => { event.preventDefault() }) as EventListener
  const pointerLockChange = (): void => {
    if (environment.document.pointerLockElement !== target) clear()
  }
  const visibilityChange = (): void => {
    if (environment.document.visibilityState === 'hidden') clear()
  }

  listen(environment.window, 'keydown', down)
  listen(environment.window, 'keyup', up)
  listen(target, 'mousemove', move)
  listen(target, 'mousedown', primary)
  listen(target, 'contextmenu', contextMenu)
  listen(environment.document, 'pointerlockchange', pointerLockChange)
  listen(environment.window, 'blur', clear)
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
    clear,
    engaged: () => environment.document.pointerLockElement === target,
    engage: () => target.requestPointerLock(),
    release: () => {
      if (environment.document.pointerLockElement === target) environment.document.exitPointerLock()
    },
    dispose: () => {
      clear()
      for (const dispose of disposers.splice(0)) dispose()
    },
  }
}
