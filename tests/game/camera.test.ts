import { describe, expect, it } from 'vitest'
import {
  FREE_SPEED,
  MAX_FRAME_SECONDS,
  MIN_ORBIT_RADIUS,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  freePoseForPersistence,
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

  it('derives an equivalent displayed free pose for persistence without changing orbit mode', () => {
    const orbit = orbitState()
    const display = displayCameraPose(orbit)

    const persisted = freePoseForPersistence(orbit)

    expect(persisted.position).toEqual(display.eye)
    expect(displayCameraPose({ mode: 'free', pose: persisted }).forward).toEqual(display.forward)
    expect(orbit).toBe(orbit)
    expect(orbit.mode).toBe('orbit')
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

  it('moves along horizontal yaw at full speed despite a steep free-flight pitch', () => {
    const start: FreeCameraState = {
      mode: 'free',
      pose: { position: { x: 0, y: 1.7, z: 0 }, yaw: -Math.PI / 2, pitch: 1.3 },
    }
    const next = stepCamera(start, { ...noInput, w: true }, 0.05)
    if (next.mode !== 'free') throw new Error('expected free camera')
    expect(next.pose.position.x - start.pose.position.x).toBeCloseTo(FREE_SPEED * 0.05)
    expect(next.pose.position.y).toBe(start.pose.position.y)
    expect(next.pose.position.z).toBeCloseTo(start.pose.position.z)
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

  it('ignores non-finite or nonpositive frame time', () => {
    for (const seconds of [Number.NaN, Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY, 0, -1]) {
      expect(stepCamera(freeState(), { ...noInput, w: true }, seconds)).toEqual(freeState())
      expect(stepCamera(orbitState(), { ...noInput, w: true }, seconds)).toEqual(orbitState())
    }
  })

  it('returns a finite display direction for a degenerate orbit pose', () => {
    const display = displayCameraPose({
      mode: 'orbit',
      orbitTarget: 'tree-a',
      pose: { center: { x: 3, y: 4, z: 5 }, radius: 0, azimuth: 0, height: 0 },
    })
    expect(display.eye).toEqual({ x: 3, y: 4, z: 5 })
    expect(Object.values(display.forward).every(Number.isFinite)).toBe(true)
  })

  it('rejects non-finite world bounds during orbit entry', () => {
    expect(() => enterOrbit(freeState(), 'tree-a', {
      center: { x: Number.NaN, y: 8, z: -4 }, radius: 6,
    })).toThrow('orbit bounds center must be finite')
    expect(() => enterOrbit(freeState(), 'tree-a', {
      center: bounds.center, radius: Number.POSITIVE_INFINITY,
    })).toThrow('orbit bounds radius must be finite and non-negative')
  })

  it('applies mouse motion only to a free pose', () => {
    const free = lookCamera(freeState(), { x: 20, y: -10 })
    const orbit = lookCamera(orbitState(), { x: 20, y: -10 })
    expect(free).not.toEqual(freeState())
    expect(orbit).toEqual(orbitState())
  })
})
