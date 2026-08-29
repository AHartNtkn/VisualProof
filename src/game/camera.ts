import type { CameraPose, TreeTarget } from './model'
import type { DisplayCameraPose } from './render/types'
import { eyeOf, type CamPose } from '../view3d/camera'
import { OrbitInteraction } from '../view3d/orbit-interaction'

export type CameraMotion = {
  readonly forward: number
  readonly strafe: number
  readonly vertical: number
  readonly sprint: boolean
  readonly lookX: number
  readonly lookY: number
}

export type CameraState =
  | { readonly mode: 'free'; readonly pose: CameraPose }
  | {
      readonly mode: 'orbit'
      readonly treeId: string
      readonly freePose: CameraPose
      readonly interaction: OrbitInteraction
    }

const LOOK_RADIANS_PER_PIXEL = 0.002
const FREE_SPEED = 8
const SPRINT_MULTIPLIER = 3
const MAX_PITCH = Math.PI / 2 - 0.01

export function initialCameraState(
  pose: CameraPose,
): { readonly mode: 'free'; readonly pose: CameraPose } {
  return { mode: 'free', pose }
}

export function advanceCamera(
  state: CameraState,
  motion: CameraMotion,
  dt: number,
): CameraState {
  if (state.mode === 'orbit') return state

  const yaw = state.pose.yaw - motion.lookX * LOOK_RADIANS_PER_PIXEL
  const pitch = Math.max(
    -MAX_PITCH,
    Math.min(MAX_PITCH, state.pose.pitch - motion.lookY * LOOK_RADIANS_PER_PIXEL),
  )
  const forward = { x: -Math.sin(yaw), y: 0, z: -Math.cos(yaw) }
  const right = { x: Math.cos(yaw), y: 0, z: -Math.sin(yaw) }
  let x = forward.x * motion.forward + right.x * motion.strafe
  let y = motion.vertical
  let z = forward.z * motion.forward + right.z * motion.strafe
  const length = Math.hypot(x, y, z)
  if (length > 1) {
    x /= length
    y /= length
    z /= length
  }
  const distance = FREE_SPEED * (motion.sprint ? SPRINT_MULTIPLIER : 1) * dt

  return {
    mode: 'free',
    pose: {
      position: {
        x: state.pose.position.x + x * distance,
        y: state.pose.position.y + y * distance,
        z: state.pose.position.z + z * distance,
      },
      yaw,
      pitch,
    },
  }
}

export function enterOrbit(
  state: { readonly mode: 'free'; readonly pose: CameraPose },
  target: TreeTarget,
): {
  readonly mode: 'orbit'
  readonly treeId: string
  readonly freePose: CameraPose
  readonly interaction: OrbitInteraction
} {
  const dx = state.pose.position.x - target.center.x
  const dy = state.pose.position.y - target.center.y
  const dz = state.pose.position.z - target.center.z
  const distance = Math.hypot(dx, dy, dz)
  const pose: CamPose = {
    target: target.center,
    dist: distance,
    yaw: Math.atan2(dx, dz),
    pitch: distance === 0 ? 0 : Math.asin(dy / distance),
  }
  return {
    mode: 'orbit',
    treeId: target.treeId,
    freePose: state.pose,
    interaction: new OrbitInteraction(pose),
  }
}

export function exitOrbit(
  state: Extract<CameraState, { readonly mode: 'orbit' }>,
): { readonly mode: 'free'; readonly pose: CameraPose } {
  return initialCameraState(state.freePose)
}

export function displayCameraPose(
  state: CameraState,
  now: number = performance.now(),
): DisplayCameraPose {
  if (state.mode === 'free') {
    const cosPitch = Math.cos(state.pose.pitch)
    return {
      eye: state.pose.position,
      forward: {
        x: -Math.sin(state.pose.yaw) * cosPitch,
        y: Math.sin(state.pose.pitch),
        z: -Math.cos(state.pose.yaw) * cosPitch,
      },
    }
  }

  const pose = state.interaction.poseAt(now)
  const eye = eyeOf(pose)
  const x = pose.target.x - eye.x
  const y = pose.target.y - eye.y
  const z = pose.target.z - eye.z
  const length = Math.hypot(x, y, z)
  return {
    eye,
    forward: { x: x / length, y: y / length, z: z / length },
  }
}

export function cameraPoseForSave(state: CameraState): CameraPose {
  return state.mode === 'free' ? state.pose : state.freePose
}
