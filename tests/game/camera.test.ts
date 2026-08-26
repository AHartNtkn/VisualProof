import { describe, expect, it } from 'vitest'
import {
  FREE_SPEED,
  MAX_FRAME_SECONDS,
  MIN_ORBIT_RADIUS,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  lookCamera,
  stepCamera,
  type CameraInput,
  type FreeCameraState,
  type OrbitCameraState,
} from '../../src/game/camera'

const noInput: CameraInput = {
  w: false, a: false, s: false, d: false, space: false, ctrl: false, shift: false,
}

const bounds = { center: { x: 10, y: 8, z: -4 }, radius: 6 }

const freeState = (): FreeCameraState => ({
  mode: 'free',
  pose: { position: { x: 0, y: 1.7, z: 20 }, yaw: 0, pitch: 0 },
})

const orbitState = (): OrbitCameraState => ({
  mode: 'orbit',
  orbitTarget: 'tree-a',
  pose: { center: bounds.center, radius: 20, azimuth: 0, height: 4 },
})

describe('camera state', () => {
  it('mirrors movement controls in free flight and orbit', () => {
    const free = stepCamera(freeState(), { ...noInput, w: true, d: true, space: true }, 1)
    expect(free.mode).toBe('free')
    if (free.mode !== 'free') throw new Error('expected free camera')
    expect(free.pose.position.y).toBeGreaterThan(1.7)

    const orbit = stepCamera(orbitState(), { ...noInput, w: true, d: true, space: true }, 1)
    expect(orbit.mode).toBe('orbit')
    if (orbit.mode !== 'orbit') throw new Error('expected orbit camera')
    expect(orbit.pose.radius).toBeLessThan(orbitState().pose.radius)
    expect(orbit.pose.azimuth).not.toBe(orbitState().pose.azimuth)
    expect(orbit.pose.height).toBeGreaterThan(orbitState().pose.height)
  })

  it('enters orbit around one tree and exits at the displayed eye and direction', () => {
    const orbit = enterOrbit(freeState(), 'tree-a', bounds)
    expect(orbit).toMatchObject({ mode: 'orbit', orbitTarget: 'tree-a' })
    const display = displayCameraPose(orbit)
    const free = exitOrbit(orbit)
    expect(free.pose.position).toEqual(display.eye)
    expect(displayCameraPose(free).forward).toEqual(display.forward)
  })

  it('normalizes diagonal free-flight movement', () => {
    const start = freeState()
    const next = stepCamera(start, { ...noInput, w: true, d: true, space: true }, 0.05)
    if (next.mode !== 'free') throw new Error('expected free camera')
    expect(Math.hypot(
      next.pose.position.x - start.pose.position.x,
      next.pose.position.y - start.pose.position.y,
      next.pose.position.z - start.pose.position.z,
    )).toBeCloseTo(FREE_SPEED * 0.05)
  })

  it('clamps free pitch and orbit radius', () => {
    const looked = lookCamera(freeState(), { x: 0, y: -1_000_000 })
    if (looked.mode !== 'free') throw new Error('expected free camera')
    expect(Math.abs(looked.pose.pitch)).toBeLessThan(Math.PI / 2)

    const close = stepCamera({
      ...orbitState(),
      pose: { ...orbitState().pose, radius: MIN_ORBIT_RADIUS },
    }, { ...noInput, w: true }, 1)
    if (close.mode !== 'orbit') throw new Error('expected orbit camera')
    expect(close.pose.radius).toBe(MIN_ORBIT_RADIUS)

  })

  it('doubles free-flight movement while sprinting', () => {
    const start = freeState()
    const walking = stepCamera(start, { ...noInput, w: true }, 0.5)
    const sprinting = stepCamera(start, { ...noInput, w: true, shift: true }, 0.5)
    if (walking.mode !== 'free' || sprinting.mode !== 'free') throw new Error('expected free camera')
    expect(Math.hypot(
      sprinting.pose.position.x - start.pose.position.x,
      sprinting.pose.position.z - start.pose.position.z,
    )).toBeCloseTo(2 * Math.hypot(
      walking.pose.position.x - start.pose.position.x,
      walking.pose.position.z - start.pose.position.z,
    ))
  })

  it('cancels opposing controls in both camera modes', () => {
    const free = stepCamera(freeState(), {
      ...noInput, w: true, s: true, a: true, d: true, space: true, ctrl: true,
    }, 1)
    expect(free).toEqual(freeState())

    const orbit = stepCamera(orbitState(), {
      ...noInput, w: true, s: true, a: true, d: true, space: true, ctrl: true,
    }, 1)
    expect(orbit).toEqual(orbitState())
  })

  it('clamps frame time before applying motion', () => {
    const start = freeState()
    const next = stepCamera(start, { ...noInput, w: true }, 1_000_000)
    if (next.mode !== 'free') throw new Error('expected free camera')
    expect(Math.hypot(
      next.pose.position.x - start.pose.position.x,
      next.pose.position.z - start.pose.position.z,
    )).toBeCloseTo(FREE_SPEED * MAX_FRAME_SECONDS)
  })

  it('applies mouse motion only to a free pose', () => {
    const free = lookCamera(freeState(), { x: 20, y: -10 })
    const orbit = lookCamera(orbitState(), { x: 20, y: -10 })
    expect(free).not.toEqual(freeState())
    expect(orbit).toEqual(orbitState())
  })
})
