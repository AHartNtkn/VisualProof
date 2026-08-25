import { describe, expect, it } from 'vitest'
import { deriveTreeLods } from '../../orchard/lod-assets'
import type { Scene3 } from '../../src/view3d/scene'

const full: Scene3 = {
  center: { x: 0, y: 5, z: 0 }, radius: 6,
  entities: [
    { kind: 'branch', key: 'b:0', polarity: 0, pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 10, z: 0 }] },
    { kind: 'strand', key: 's:w:0', wire: 'w', pts: [{ x: 0, y: 2, z: 0 }, { x: 2, y: 4, z: 0 }] },
    { kind: 'pip', key: 'p:n', node: 'n', ownerWire: 'w', pos: { x: 0, y: 2, z: 0 } },
  ],
}

describe('deriveTreeLods', () => {
  it('keeps full geometry exact and derives a branch-only reduced asset', () => {
    const lods = deriveTreeLods(full)
    expect(lods.full).toEqual(full)
    expect(lods.reduced.entities.map(({ key }) => key)).toEqual(['b:0'])
    expect(lods.marker).toEqual({ color: '#e6e1d6', size: 1.2 })
  })
})
