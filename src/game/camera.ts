import type { FreeCameraPose } from './model'
import type { DisplayCameraPose } from './render/types'
import type { Vec3 } from '../view3d/vec3'

export type OrbitCameraPose = {
  readonly center: Vec3
  readonly radius: number
  readonly azimuth: number
  readonly height: number
}

export type FreeCameraState = { readonly mode: 'free'; readonly pose: FreeCameraPose }
export type OrbitCameraState = {
  readonly mode: 'orbit'
  readonly orbitTarget: string
  readonly pose: OrbitCameraPose
}
export type CameraState = FreeCameraState | OrbitCameraState

export type CameraInput = {
  readonly w: boolean
  readonly a: boolean
  readonly s: boolean
  readonly d: boolean
  readonly space: boolean
  readonly ctrl: boolean
  readonly shift: boolean
}

export type CameraLookDelta = { readonly x: number; readonly y: number }
export type TreeWorldBounds = { readonly center: Vec3; readonly radius: number }

export const INTERACTION_REACH = 100
export const FREE_SPEED = 12
export const SPRINT_MULTIPLIER = 2
export const ORBIT_ANGULAR_SPEED = 1.2
export const ORBIT_RADIAL_SPEED = 18
export const ORBIT_VERTICAL_SPEED = 12

export const MAX_FRAME_SECONDS = 0.1
export const FREE_PITCH_LIMIT = 1.35
export const MIN_ORBIT_RADIUS = 2

const LOOK_SENSITIVITY = 0.0022
const ORBIT_FRAME_RADIUS = 2

function clamp(value: number, low: number, high: number): number {
  return Math.max(low, Math.min(high, value))
}

function clampedFrameSeconds(seconds: number): number {
  return clamp(seconds, 0, MAX_FRAME_SECONDS)
}

function axis(positive: boolean, negative: boolean): number {
  return Number(positive) - Number(negative)
}

function unitMovement(forward: number, right: number, vertical: number): Vec3 {
  const length = Math.hypot(forward, right, vertical)
  return length === 0
    ? { x: 0, y: 0, z: 0 }
    : { x: forward / length, y: vertical / length, z: right / length }
}

function freeForward(pose: FreeCameraPose): Vec3 {
  const horizontal = Math.cos(pose.pitch)
  return {
    x: -Math.sin(pose.yaw) * horizontal,
    y: Math.sin(pose.pitch),
    z: -Math.cos(pose.yaw) * horizontal,
  }
}

function orbitEye(pose: OrbitCameraPose): Vec3 {
  return {
    x: pose.center.x + Math.sin(pose.azimuth) * pose.radius,
    y: pose.center.y + pose.height,
    z: pose.center.z + Math.cos(pose.azimuth) * pose.radius,
  }
}

function orbitForward(pose: OrbitCameraPose): Vec3 {
  const eye = orbitEye(pose)
  const x = pose.center.x - eye.x
  const y = pose.center.y - eye.y
  const z = pose.center.z - eye.z
  const length = Math.hypot(x, y, z)
  const forward = { x: x / length, y: y / length, z: z / length }
  return freeForward({
    position: eye,
    yaw: Math.atan2(-forward.x, -forward.z),
    pitch: Math.asin(forward.y),
  })
}

export function stepCamera(state: CameraState, input: CameraInput, seconds: number): CameraState {
  const elapsed = clampedFrameSeconds(seconds)
  if (state.mode === 'orbit') {
    const radiusDirection = axis(input.s, input.w)
    return {
      ...state,
      pose: {
        ...state.pose,
        azimuth: state.pose.azimuth + axis(input.d, input.a) * ORBIT_ANGULAR_SPEED * elapsed,
        radius: Math.max(
          MIN_ORBIT_RADIUS,
          state.pose.radius + radiusDirection * ORBIT_RADIAL_SPEED * elapsed,
        ),
        height: state.pose.height + axis(input.space, input.ctrl) * ORBIT_VERTICAL_SPEED * elapsed,
      },
    }
  }

  const movement = unitMovement(axis(input.w, input.s), axis(input.d, input.a), axis(input.space, input.ctrl))
  const speed = FREE_SPEED * (input.shift ? SPRINT_MULTIPLIER : 1) * elapsed
  const forward = freeForward(state.pose)
  const right = { x: Math.cos(state.pose.yaw), y: 0, z: -Math.sin(state.pose.yaw) }
  return {
    mode: 'free',
    pose: {
      ...state.pose,
      position: {
        x: state.pose.position.x + (forward.x * movement.x + right.x * movement.z) * speed,
        y: state.pose.position.y + movement.y * speed,
        z: state.pose.position.z + (forward.z * movement.x + right.z * movement.z) * speed,
      },
    },
  }
}

export function lookCamera(state: CameraState, delta: CameraLookDelta): CameraState {
  if (state.mode === 'orbit') return state
  return {
    mode: 'free',
    pose: {
      ...state.pose,
      yaw: state.pose.yaw - delta.x * LOOK_SENSITIVITY,
      pitch: clamp(state.pose.pitch - delta.y * LOOK_SENSITIVITY, -FREE_PITCH_LIMIT, FREE_PITCH_LIMIT),
    },
  }
}

export function enterOrbit(
  state: FreeCameraState,
  orbitTarget: string,
  bounds: TreeWorldBounds,
): OrbitCameraState {
  const eye = displayCameraPose(state).eye
  const x = eye.x - bounds.center.x
  const z = eye.z - bounds.center.z
  const radius = Math.max(MIN_ORBIT_RADIUS, Math.hypot(x, z), bounds.radius * ORBIT_FRAME_RADIUS)
  return {
    mode: 'orbit',
    orbitTarget,
    pose: {
      center: bounds.center,
      radius,
      azimuth: Math.atan2(x, z),
      height: eye.y - bounds.center.y,
    },
  }
}

export function displayCameraPose(state: CameraState): DisplayCameraPose {
  if (state.mode === 'free') return { eye: state.pose.position, forward: freeForward(state.pose) }
  return { eye: orbitEye(state.pose), forward: orbitForward(state.pose) }
}

export function exitOrbit(state: CameraState): FreeCameraState {
  if (state.mode === 'free') return state
  const display = displayCameraPose(state)
  return {
    mode: 'free',
    pose: {
      position: display.eye,
      yaw: Math.atan2(-display.forward.x, -display.forward.z),
      pitch: Math.asin(display.forward.y),
    },
  }
}
