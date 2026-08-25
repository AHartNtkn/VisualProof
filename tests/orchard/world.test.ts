import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { parseWorldSave } from '../../orchard/world'

describe('orchard world save', () => {
  it('owns the complete terrain, player, tree, and precomputed layout state', () => {
    const raw = JSON.parse(readFileSync(new URL('../../orchard/world.json', import.meta.url), 'utf8'))
    const world = parseWorldSave(raw)

    expect(world.version).toBe(1)
    expect(world.terrain).toEqual({
      size: 4000,
      ground: '#4f8f3b',
      sky: '#a9d5ec',
      fogNear: 170,
      fogFar: 780,
      bounds: { minX: -2000, maxX: 2000, minZ: -2000, maxZ: 2000 },
    })
    expect(world.player).toEqual({ x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 })
    expect(world.trees).toHaveLength(2000)
    expect(new Set(world.trees.map(({ id }) => id)).size).toBe(2000)
    expect(world.trees[0]).toEqual({
      id: 'tree-0000',
      layout: 'zero-is-nat-20',
      x: 0,
      z: 0,
      yaw: 0,
    })

    const layout = world.layouts['zero-is-nat-20']!
    expect(layout.label).toBe('zeroIsNat · step 20')
    expect(layout.scene.entities).toHaveLength(73)
    expect(layout.scene.entities.filter(({ kind }) => kind === 'branch')).toHaveLength(17)
    expect(layout.scene.entities.filter(({ kind }) => kind === 'strand')).toHaveLength(41)
    for (const tree of world.trees) expect(world.layouts[tree.layout]).toBeDefined()
  })
})
