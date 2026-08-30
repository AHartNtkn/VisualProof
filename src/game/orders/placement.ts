import type { DisplayCameraPose } from '../render/types'
import type { PotPlacement } from './catalog'
import { SPROUT_CLEARANCE } from '../placement'

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

export function availablePotPlacementAhead(
  pose: DisplayCameraPose,
  distance: number,
  occupied: readonly Pick<PotPlacement, 'x' | 'z'>[],
  clearance = SPROUT_CLEARANCE,
): PotPlacement {
  if (!Number.isFinite(clearance) || clearance <= 0) {
    throw new Error('pot clearance must be finite and positive')
  }
  const center = potPlacementAhead(pose, distance)
  const length = Math.hypot(pose.forward.x, pose.forward.z)
  const right = { x: -pose.forward.z / length, z: pose.forward.x / length }
  const clear = (candidate: PotPlacement): boolean => occupied.every((pot) => {
    if (!Number.isFinite(pot.x) || !Number.isFinite(pot.z)) {
      throw new Error('occupied pot coordinates must be finite')
    }
    return Math.hypot(candidate.x - pot.x, candidate.z - pot.z) >= clearance
  })
  if (clear(center)) return center
  for (let step = 1; ; step += 1) {
    for (const direction of [1, -1] as const) {
      const candidate = {
        x: center.x + right.x * clearance * step * direction,
        z: center.z + right.z * clearance * step * direction,
        yaw: center.yaw,
      }
      if (clear(candidate)) return candidate
    }
  }
}
