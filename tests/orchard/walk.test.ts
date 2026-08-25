import { describe, expect, it } from 'vitest'
import { clampGroundPosition, stepWalker } from '../../orchard/walk'

describe('stepWalker', () => {
  it('moves forward and sideways relative to the view yaw', () => {
    expect(stepWalker({ x: 0, z: 0 }, { forward: true }, 1, 0)).toEqual({ x: 0, z: -6 })

    const turned = stepWalker({ x: 0, z: 0 }, { forward: true }, 1, -Math.PI / 2)
    expect(turned.x).toBeCloseTo(6)
    expect(turned.z).toBeCloseTo(0)
  })

  it('normalizes diagonal input to the same walking speed', () => {
    const next = stepWalker({ x: 2, z: 3 }, { forward: true, right: true }, 1, 0)

    expect(Math.hypot(next.x - 2, next.z - 3)).toBeCloseTo(6)
  })

  it('sprints at twice walking speed and opposing keys cancel', () => {
    expect(stepWalker({ x: 0, z: 0 }, { forward: true, sprint: true }, 0.5, 0)).toEqual({ x: 0, z: -6 })
    expect(stepWalker(
      { x: 4, z: 5 },
      { forward: true, backward: true, left: true, right: true },
      1,
      0,
    )).toEqual({ x: 4, z: 5 })
  })

  it('clamps the player to the saved world bounds', () => {
    expect(clampGroundPosition(
      { x: 12, z: -9 },
      { minX: -5, maxX: 8, minZ: -7, maxZ: 10 },
    )).toEqual({ x: 8, z: -7 })
  })
})
