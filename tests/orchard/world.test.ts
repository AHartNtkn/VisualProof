import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { parseWorldSave } from '../../orchard/world'

describe('orchard world save', () => {
  it('owns the complete terrain, player, tree, and precomputed layout state', () => {
    const raw = JSON.parse(readFileSync(new URL('../../orchard/world.json', import.meta.url), 'utf8'))
    const world = parseWorldSave(raw)

    expect(world.version).toBe(2)
    expect(world.terrain).toEqual({
      size: 4000,
      ground: '#080a0c',
      sky: '#000000',
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
    expect(layout.palette).toEqual({ branch: '#e6e1d6', cutBranch: '#4a5058', baseWire: '#5bd2de' })
    expect(layout.widths).toEqual({ branch: 0.10, curve: 0.05 })
    expect(layout.glow).toEqual({ color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 })
    expect(layout.lods.full.entities).toHaveLength(73)
    expect(layout.lods.reduced.entities.every(({ kind }) => kind === 'branch')).toBe(true)
    expect(layout.lods.marker).toEqual({ color: '#e6e1d6', size: 1.2 })
    expect(layout.lods.full.entities.filter(({ kind }) => kind === 'branch')).toHaveLength(17)
    expect(layout.lods.full.entities.filter(({ kind }) => kind === 'strand')).toHaveLength(41)
    for (const tree of world.trees) expect(world.layouts[tree.layout]).toBeDefined()
  })

  it.each([
    ['version 1', (raw: any) => { raw.version = 1 }, 'invalid orchard save: version'],
    ['missing LODs', (raw: any) => { delete raw.layouts['zero-is-nat-20'].lods }, 'invalid orchard save: layouts.zero-is-nat-20'],
    ['missing reduced LOD', (raw: any) => { delete raw.layouts['zero-is-nat-20'].lods.reduced }, 'invalid orchard save: layouts.zero-is-nat-20.lods.reduced'],
    ['missing marker size', (raw: any) => { delete raw.layouts['zero-is-nat-20'].lods.marker.size }, 'invalid orchard save: layouts.zero-is-nat-20.lods.marker.size'],
    ['missing glow', (raw: any) => { delete raw.layouts['zero-is-nat-20'].glow }, 'invalid orchard save: layouts.zero-is-nat-20'],
    ['missing bloom', (raw: any) => { delete raw.layouts['zero-is-nat-20'].glow.bloom }, 'invalid orchard save: layouts.zero-is-nat-20.glow.bloom'],
    ['out-of-range bloom', (raw: any) => { raw.layouts['zero-is-nat-20'].glow.bloom = 1.01 }, 'invalid orchard save: layouts.zero-is-nat-20.glow.bloom'],
    ['out-of-range opacity', (raw: any) => { raw.layouts['zero-is-nat-20'].glow.opacity = 1.01 }, 'invalid orchard save: layouts.zero-is-nat-20.glow.opacity'],
    ['non-branch reduced entity', (raw: any) => {
      raw.layouts['zero-is-nat-20'].lods.reduced.entities = [
        raw.layouts['zero-is-nat-20'].lods.full.entities.find((entity: any) => entity.kind === 'ring'),
      ]
    }, 'invalid orchard save: layouts.zero-is-nat-20.lods.reduced.entities[0].kind'],
  ])('rejects %s', (_name, mutate, error) => {
    const raw = JSON.parse(readFileSync(new URL('../../orchard/world.json', import.meta.url), 'utf8'))
    mutate(raw)

    expect(() => parseWorldSave(raw)).toThrow(error)
  })
})
