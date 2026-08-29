import type { DisplayCameraPose } from '../render/types'
import type { PotPlacement } from './catalog'

export function potPlacementAhead(pose: DisplayCameraPose, distance: number): PotPlacement {
  if (!Number.isFinite(distance) || distance <= 0) {
    throw new Error('pot placement distance must be finite and positive')
  }
  if (!Number.isFinite(pose.eye.x) || !Number.isFinite(pose.eye.z)) {
    throw new Error('camera eye must have finite horizontal coordinates')
  }
  if (!Number.isFinite(pose.forward.x) || !Number.isFinite(pose.forward.z)) {
    throw new Error('camera forward vector must have finite horizontal coordinates')
  }

  const length = Math.hypot(pose.forward.x, pose.forward.z)
  if (length === 0) throw new Error('camera forward vector must have a horizontal direction')
  const x = pose.forward.x / length
  const z = pose.forward.z / length
  const yaw = Math.atan2(-x, -z)
  return {
    x: pose.eye.x + x * distance,
    z: pose.eye.z + z * distance,
    yaw: Object.is(yaw, -0) ? 0 : yaw,
  }
}
