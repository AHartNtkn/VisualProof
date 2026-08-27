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
  public readonly positions: Array<{ readonly x: number; readonly y: number }> = []
  public captureChanges = 0

  public async setCaptured(captured: boolean): Promise<void> {
    this.captured = captured
    this.captureChanges++
  }

  public async setCursorVisible(visible: boolean): Promise<void> {
    this.visible = visible
  }

  public async setCursorPosition(position: { readonly x: number; readonly y: number }): Promise<void> {
    this.positions.push(position)
  }
}

function canvasForMouse(): {
  readonly canvas: HTMLCanvasElement
  move(x: number, y: number): void
} {
  let listener: ((event: MouseEvent) => void) | null = null
  return {
    canvas: {
      addEventListener(type: string, callback: EventListenerOrEventListenerObject) {
        if (type === 'mousemove' && typeof callback === 'function') listener = callback as (event: MouseEvent) => void
      },
      removeEventListener(type: string) {
        if (type === 'mousemove') listener = null
      },
      getBoundingClientRect: () => ({ left: 20, top: 30, width: 160, height: 80 }),
    } as unknown as HTMLCanvasElement,
    move(x, y) {
      listener?.({ clientX: x, clientY: y } as MouseEvent)
    },
  }
}

describe('desktop mouse', () => {
  it('turns displacement around the viewport center into relative flight motion and ignores recentering', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    const motions: Array<{ readonly x: number; readonly y: number }> = []
    const mouse = new DesktopMouse(fixture.canvas, native, (delta) => motions.push(delta))

    await mouse.capture()
    fixture.move(112, 66)
    fixture.move(100, 70)

    expect(motions).toEqual([{ x: 12, y: -4 }])
    expect(native.positions).toEqual([{ x: 100, y: 70 }, { x: 100, y: 70 }])
  })

  it('keeps native capture and cursor state stable across repeated capture and release', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
    const mouse = new DesktopMouse(fixture.canvas, native, () => {})

    await mouse.capture()
    await mouse.capture()
    await mouse.release()
    await mouse.release()

    expect(native.captureChanges).toBe(2)
    expect(native.captured).toBe(false)
    expect(native.visible).toBe(true)
  })

  it('leaves the displayed orbit pose unchanged when native motion arrives during the orbit handoff', async () => {
    const native = new NativeMouse()
    const fixture = canvasForMouse()
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
