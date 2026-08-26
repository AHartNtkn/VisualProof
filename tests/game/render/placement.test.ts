import { describe, expect, it } from 'vitest'
import { orchardPlacements } from '../../../src/game/render/placement'

describe('orchardPlacements', () => {
  it('lays out stable tree records progressively from the world center', () => {
    const placements = orchardPlacements(5, 10)

    expect(placements.map(({ id, index, x, z }) => ({ id, index, x, z }))).toEqual([
      { id: 'tree-0000', index: 0, x: 0, z: 0 },
      { id: 'tree-0001', index: 1, x: 10, z: 0 },
      { id: 'tree-0002', index: 2, x: 10, z: 10 },
      { id: 'tree-0003', index: 3, x: 0, z: 10 },
      { id: 'tree-0004', index: 4, x: -10, z: 10 },
    ])
  })

  it('keeps every pair of trees at least one spacing apart', () => {
    const placements = orchardPlacements(37, 18)

    for (let i = 0; i < placements.length; i++) {
      for (let j = i + 1; j < placements.length; j++) {
        const a = placements[i]!, b = placements[j]!
        expect(Math.hypot(a.x - b.x, a.z - b.z)).toBeGreaterThanOrEqual(18)
      }
    }
  })

  it('gives trees varied but repeatable rotations', () => {
    const first = orchardPlacements(12, 18)
    const second = orchardPlacements(12, 18)

    expect(first).toEqual(second)
    expect(new Set(first.map(({ yaw }) => yaw)).size).toBeGreaterThan(8)
    for (const { yaw } of first) {
      expect(yaw).toBeGreaterThanOrEqual(0)
      expect(yaw).toBeLessThan(Math.PI * 2)
    }
  })

  it('rejects counts that cannot describe a finite collection of trees', () => {
    expect(() => orchardPlacements(-1, 10)).toThrow('non-negative integer')
    expect(() => orchardPlacements(1.5, 10)).toThrow('non-negative integer')
    expect(() => orchardPlacements(Number.POSITIVE_INFINITY, 10)).toThrow('non-negative integer')
  })
})
