import { describe, expect, it } from 'vitest'
import { GlowTilePlan } from '../../../src/game/render/glow-tiles'

describe('GlowTilePlan', () => {
  it('dirties every overlapped tile for arbitrary inserts, moves, and removals', () => {
    const plan = new GlowTilePlan(128)
    plan.set({ id: 'a', x: 127, z: 0, radius: 32, color: '#fff', opacity: 0.6 })
    expect(plan.flushDirty().map(({ key }) => key)).toEqual(['0:-1', '0:0', '1:-1', '1:0'])

    plan.move('a', -129, -129)
    expect(plan.flushDirty().map(({ key }) => key)).toEqual([
      '-1:-1', '-1:-2', '-2:-1', '-2:-2', '0:-1', '0:0', '1:-1', '1:0',
    ])

    plan.remove('a')
    expect(plan.flushDirty().map(({ key }) => key)).toEqual(['-1:-1', '-1:-2', '-2:-1', '-2:-2'])
  })

  it('returns all dense-cluster contributors intersecting a tile', () => {
    const plan = new GlowTilePlan(128)
    for (let index = 0; index < 50; index++) {
      plan.set({ id: String(index), x: index % 5, z: index % 7, radius: 32, color: '#fff', opacity: 0.2 })
    }
    expect(plan.contributors('0:0')).toHaveLength(50)
  })

  it('upserts a replacement contribution and dirties its old and new tile coverage', () => {
    const plan = new GlowTilePlan(128)
    plan.set({ id: 'a', x: 0, z: 0, radius: 8, color: '#fff', opacity: 0.2 })
    plan.flushDirty()

    plan.set({ id: 'a', x: 240, z: 240, radius: 12, color: '#f0f', opacity: 0.7 })
    expect(plan.flushDirty()).toEqual([
      { key: '-1:-1', x: -1, z: -1, contributors: [] },
      { key: '-1:0', x: -1, z: 0, contributors: [] },
      { key: '0:-1', x: 0, z: -1, contributors: [] },
      { key: '0:0', x: 0, z: 0, contributors: [] },
      {
        key: '1:1', x: 1, z: 1,
        contributors: [{ id: 'a', x: 240, z: 240, radius: 12, color: '#f0f', opacity: 0.7 }],
      },
    ])
  })

  it('does not dirty a tile that only the glow bounding box reaches at a corner', () => {
    const plan = new GlowTilePlan(128)
    plan.set({ id: 'corner', x: 120, z: 120, radius: 10, color: '#fff', opacity: 0.5 })

    expect(plan.flushDirty().map(({ key }) => key)).toEqual(['0:0', '0:1', '1:0'])
  })

  it('has no dirty tiles without a further entity event', () => {
    const plan = new GlowTilePlan(128)
    plan.set({ id: 'a', x: 20, z: 20, radius: 8, color: '#fff', opacity: 0.5 })
    plan.flushDirty()

    expect(plan.flushDirty()).toEqual([])
  })
})
