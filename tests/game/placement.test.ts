import { describe, expect, it } from 'vitest'
import { SPROUT_CLEARANCE, requireClearSproutPlacement } from '../../src/game/placement'

describe('sprout placement clearance', () => {
  it('rejects placements closer than the clearance radius to trees and pots', () => {
    expect(() => requireClearSproutPlacement(
      { x: SPROUT_CLEARANCE - 0.001, z: 0 },
      [{ kind: 'tree', id: 'tree-a', x: 0, z: 0 }],
    )).toThrow(/tree 'tree-a'/)
    expect(() => requireClearSproutPlacement(
      { x: 10 - SPROUT_CLEARANCE + 0.001, z: 0 },
      [{ kind: 'pot', id: 'order-a', x: 10, z: 0 }],
    )).toThrow(/pot 'order-a'/)
  })

  it('accepts placements exactly at the clearance radius', () => {
    expect(() => requireClearSproutPlacement(
      { x: SPROUT_CLEARANCE, z: 0 },
      [{ kind: 'tree', id: 'tree-a', x: 0, z: 0 }],
    )).not.toThrow()
    expect(() => requireClearSproutPlacement(
      { x: 10 - SPROUT_CLEARANCE, z: 0 },
      [{ kind: 'pot', id: 'order-a', x: 10, z: 0 }],
    )).not.toThrow()
  })

  it('rejects nonfinite ground coordinates', () => {
    expect(() => requireClearSproutPlacement({ x: Number.NaN, z: 0 }, []))
      .toThrow(/finite ground coordinates/)
    expect(() => requireClearSproutPlacement({ x: 0, z: Number.POSITIVE_INFINITY }, []))
      .toThrow(/finite ground coordinates/)
  })
})
