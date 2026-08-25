import { describe, expect, it } from 'vitest'
import { SpatialIndex } from '../../orchard/spatial-index'

type Item = { id: string; x: number; z: number }

describe('SpatialIndex', () => {
  it('indexes clustered, sparse, negative, moved, and removed placements', () => {
    const index = new SpatialIndex<Item>(128)
    index.insert({ id: 'a', x: -129, z: -1 })
    index.insert({ id: 'b', x: 2, z: 3 })
    index.insert({ id: 'c', x: 3, z: 4 })
    expect(index.query({ minX: -140, maxX: 4, minZ: -10, maxZ: 5 }).map(({ id }) => id).sort()).toEqual(['a', 'b', 'c'])
    index.move('a', 500, 500)
    index.remove('b')
    expect(index.query({ minX: -200, maxX: 10, minZ: -20, maxZ: 20 }).map(({ id }) => id)).toEqual(['c'])
    expect(index.query({ minX: 490, maxX: 510, minZ: 490, maxZ: 510 }).map(({ id }) => id)).toEqual(['a'])
  })

  it('returns an item only when its exact position is inside the query bounds', () => {
    const index = new SpatialIndex<Item>(10)
    index.insert({ id: 'edge', x: 9.99, z: -10.01 })
    index.insert({ id: 'inside', x: 10, z: -10 })

    expect(index.query({ minX: 10, maxX: 20, minZ: -10, maxZ: 0 }).map(({ id }) => id)).toEqual(['inside'])
  })
})
