import { describe, expect, it } from 'vitest'
import {
  displayCameraPose,
  enterOrbit,
  lookCamera,
  type CameraState,
  type FreeCameraState,
} from '../../src/game/camera'
import { DesktopMouse, type DesktopMousePort } from '../../src/game/desktop-mouse'

class NativeMouse implements DesktopMousePort {
  public captured = false
  public visible = true
  public failRelease = false
  public onPosition: ((position: { readonly x: number; readonly y: number }) => void) | null = null

  public async setCaptured(captured: boolean): Promise<void> {
    if (!captured && this.failRelease) throw new Error('native release failed')
    this.captured = captured
  }

  public async setCursorVisible(visible: boolean): Promise<void> {
    this.visible = visible
  }

  public async setCursorPosition(position: { readonly x: number; readonly y: number }): Promise<void> {
    this.onPosition?.(position)
  }
}

function canvasForMouse(): {
  readonly canvas: HTMLCanvasElement
  move(x: number, y: number, screenX?: number, screenY?: number): void
  resize(width: number, height: number): void
} {
  let listener: ((event: MouseEvent) => void) | null = null
  let width = 160
  let height = 80
  return {
    canvas: {
      addEventListener(type: string, callback: EventListenerOrEventListenerObject) {
        if (type === 'mousemove' && typeof callback === 'function') listener = callback as (event: MouseEvent) => void
      },
      removeEventListener(type: string) {
        if (type === 'mousemove') listener = null
      },
      getBoundingClientRect: () => ({ left: 20, top: 30, width, height }),
    } as unknown as HTMLCanvasElement,
    move(x, y, screenX = x, screenY = y) {
      listener?.({ clientX: x, clientY: y, screenX, screenY } as MouseEvent)
    },
    resize(nextWidth, nextHeight) {
      width = nextWidth
      height = nextHeight
    },
  }
}

describe('desktop mouse', () => {
  it('turns displacement around the viewport center into relative flight motion and ignores recentering', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.move(112, 66)
    fixture.move(100, 70)

    expect(motions).toEqual([{ x: 12, y: -4 }])
    expect(native.captured).toBe(true)
    expect(native.visible).toBe(false)
  })

  it('keeps native capture and cursor state stable across repeated capture and release', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    await mouse.capture()
    fixture.move(112, 66)

    expect(native.captured).toBe(true)
    expect(native.visible).toBe(false)
    expect(motions).toEqual([{ x: 12, y: -4 }])

    await mouse.release()
    await mouse.release()
    fixture.move(112, 66)

    expect(native.captured).toBe(false)
    expect(native.visible).toBe(true)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('keeps free-flight motion captured when native release fails', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    native.failRelease = true

    await expect(mouse.release()).rejects.toThrow('native release failed')
    fixture.move(112, 66)

    expect(native.captured).toBe(true)
    expect(native.visible).toBe(false)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('does not turn the camera for pointer events emitted by native recentering', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    native.onPosition = (position) => {
      fixture.move(150, 60)
      queueMicrotask(() => fixture.move(position.x, position.y))
    }
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    expect(motions).toEqual([])

    native.onPosition = null
    fixture.move(112, 66)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('does not turn the camera when a resize changes the canvas center around a stationary pointer', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.resize(200, 100)
    fixture.move(100, 70)

    expect(motions).toEqual([])

    fixture.move(132, 76)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('does not turn the camera when a window move changes client coordinates under a stationary pointer', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y, position.x + 400, position.y + 300)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.move(-700, -330, 500, 370)

    expect(motions).toEqual([])
  })

  it('refreshes confinement after a window change without turning the camera', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.resize(200, 100)
    await mouse.refreshCapture()

    expect(native.captured).toBe(true)
    expect(native.visible).toBe(false)
    expect(motions).toEqual([])

    fixture.move(132, 76)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('applies the final bounds after another window change arrives during refresh', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.resize(180, 90)
    native.onPosition = () => {}
    const firstRefresh = mouse.refreshCapture()
    await Promise.resolve()

    fixture.resize(200, 100)
    native.onPosition = (position) => fixture.move(position.x, position.y)
    const finalRefresh = mouse.refreshCapture()
    await Promise.all([firstRefresh, finalRefresh])

    expect(motions).toEqual([])
    fixture.move(132, 76)
    expect(motions).toEqual([{ x: 12, y: -4 }])
  })

  it('leaves the displayed orbit pose unchanged when native motion arrives during the orbit handoff', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    native.onPosition = (position) => fixture.move(position.x, position.y)
    let camera: CameraState = {
      mode: 'free',
      pose: { position: { x: 0, y: 1.7, z: 20 }, yaw: 0, pitch: 0 },
    }
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => {
      camera = lookCamera(camera, delta)
    })

    await mouse.capture()
    fixture.move(112, 66)
    if (camera.mode !== 'free') throw new Error('expected free camera before orbit')
    camera = enterOrbit(camera as FreeCameraState, 'tree-a', {
      center: { x: 0, y: 0, z: 0 }, radius: 2,
    })
    const displayedBefore = displayCameraPose(camera)
    const orbitBefore = { orbitTarget: camera.orbitTarget, pose: { ...camera.pose } }

    fixture.move(88, 74)

    expect(camera).toEqual({ mode: 'orbit', ...orbitBefore })
    expect(displayCameraPose(camera)).toEqual(displayedBefore)
  })
})
