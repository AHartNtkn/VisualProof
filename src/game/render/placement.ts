export type TreePlacement = {
  readonly id: string
  readonly index: number
  readonly x: number
  readonly z: number
  readonly yaw: number
}

export function orchardPlacements(count: number, spacing: number): TreePlacement[] {
  if (!Number.isInteger(count) || count < 0) {
    throw new Error('tree count must be a non-negative integer')
  }
  if (!(spacing > 0) || !Number.isFinite(spacing)) {
    throw new Error('tree spacing must be finite and positive')
  }
  if (count === 0) return []

  const placements: TreePlacement[] = []
  let cellX = 0, cellZ = 0
  let directionX = 1, directionZ = 0
  let legLength = 1, legProgress = 0, legsAtLength = 0
  for (let index = 0; index < count; index++) {
    placements.push({
      id: `tree-${String(index).padStart(4, '0')}`,
      index,
      x: cellX * spacing,
      z: cellZ * spacing,
      yaw: (index * 2.399963229728653) % (Math.PI * 2),
    })
    cellX += directionX
    cellZ += directionZ
    legProgress++
    if (legProgress === legLength) {
      ;[directionX, directionZ] = [-directionZ, directionX]
      legProgress = 0
      legsAtLength++
      if (legsAtLength === 2) {
        legsAtLength = 0
        legLength++
      }
    }
  }
  return placements
}
