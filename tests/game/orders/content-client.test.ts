import { describe, expect, it } from 'vitest'
import {
  serializeOrderCatalog,
} from '../../../src/game/orders/content-client'
import { openingOrderCatalog } from '../../../src/game/orders/catalog'

describe('order content client', () => {
  // This catches serializing authoritative diagrams as nested JSON strings.
  it('serializes a decoded revision with parsed diagram objects', () => {
    const definitions = serializeOrderCatalog(openingOrderCatalog.current)

    expect(definitions[0]).toEqual({
      id: 'blank-sprout',
      prerequisites: [],
      reward: 1,
      goal: {
        root: 'r0',
        regions: { r0: { kind: 'sheet' } },
        nodes: {},
        wires: {},
      },
    })
    expect(typeof definitions[0]?.goal).toBe('object')
  })

})
