export const SPROUT_CLEARANCE = 4

export type PlacementObstacle = {
  readonly kind: 'tree' | 'pot'
  readonly id: string
  readonly x: number
  readonly z: number
}

export function requireClearSproutPlacement(
  point: { readonly x: number; readonly z: number },
  obstacles: readonly PlacementObstacle[],
): void {
  if (!Number.isFinite(point.x) || !Number.isFinite(point.z)) {
    throw new Error('sprout placement requires finite ground coordinates')
  }
  for (const obstacle of obstacles) {
    if (Math.hypot(point.x - obstacle.x, point.z - obstacle.z) < SPROUT_CLEARANCE) {
      throw new Error(`sprout placement is too close to ${obstacle.kind} '${obstacle.id}'`)
    }
  }
}
