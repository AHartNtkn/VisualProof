import { describe, expect, it } from 'vitest'
import { SPROUT_CLEARANCE } from '../../../src/game/placement'
import { availablePotPlacementAhead, potPlacementAhead } from '../../../src/game/orders/placement'

describe('pot placement ahead of the display camera', () => {
  it('places a pot six units ahead and faces it toward the camera', () => {
    // Catches a placement implementation that reverses the horizontal forward vector or yaw.
    expect(potPlacementAhead({
      eye: { x: 1, y: 7, z: 2 },
      forward: { x: 0, y: 0, z: -1 },
    }, 6)).toEqual({ x: 1, z: -4, yaw: 0 })
  })

  it('normalizes only the horizontal view direction', () => {
    // Catches an implementation that lets pitch shorten the ground placement direction.
    expect(potPlacementAhead({
      eye: { x: 2, y: 3, z: 5 },
      forward: { x: 3, y: 40, z: 4 },
    }, 10)).toEqual({ x: 8, z: 13, yaw: Math.atan2(-3, -4) })
  })

  it('rejects a vertical view without inventing a ground direction', () => {
    // Catches an implementation that substitutes a default direction for a vertical camera.
    expect(() => potPlacementAhead({
      eye: { x: 0, y: 2, z: 0 },
      forward: { x: 0, y: -1, z: 0 },
    }, 6)).toThrow(/horizontal/i)
  })

  it('deterministically allocates distinct clear pots from the same view', () => {
    // Catches parallel accepted orders occupying one target and becoming indistinguishable.
    const view = {
      eye: { x: 0, y: 2, z: 0 },
      forward: { x: 0, y: 0, z: -1 },
    }
    const first = availablePotPlacementAhead(view, 6, [])
    const second = availablePotPlacementAhead(view, 6, [first])
    const repeated = availablePotPlacementAhead(view, 6, [first])

    expect(first).toEqual({ x: 0, z: -6, yaw: 0 })
    expect(second).toEqual({ x: SPROUT_CLEARANCE, z: -6, yaw: 0 })
    expect(repeated).toEqual(second)
    expect(Math.hypot(second.x - first.x, second.z - first.z)).toBeGreaterThanOrEqual(SPROUT_CLEARANCE)
  })
})
