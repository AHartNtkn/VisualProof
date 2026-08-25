export type GroundPosition = { readonly x: number; readonly z: number }

export type WalkInput = {
  readonly forward?: boolean
  readonly backward?: boolean
  readonly left?: boolean
  readonly right?: boolean
  readonly sprint?: boolean
}

const WALK_SPEED = 6

export function stepWalker(
  position: GroundPosition,
  input: WalkInput,
  elapsedSeconds: number,
  yaw: number,
): GroundPosition {
  const forward = Number(input.forward === true) - Number(input.backward === true)
  const right = Number(input.right === true) - Number(input.left === true)
  const magnitude = Math.hypot(forward, right)
  if (magnitude === 0) return position

  const distance = WALK_SPEED * (input.sprint === true ? 2 : 1) * elapsedSeconds
  const along = (forward / magnitude) * distance
  const across = (right / magnitude) * distance
  return {
    x: position.x - Math.sin(yaw) * along + Math.cos(yaw) * across,
    z: position.z - Math.cos(yaw) * along - Math.sin(yaw) * across,
  }
}
