import { describe, expect, it } from 'vitest'
import { snapshotFromDiagram, snapshotFromJson } from '../../src/game/diagram-snapshot'
import { decodeLoadedSlot } from '../../src/game/model'
import { decodeCreatedSlot, decodeSlotList } from '../../src/game/save-client'
import { openingOrderCatalog, type OrderCatalogRevision } from '../../src/game/orders/catalog'
import { diagramToJson } from '../../src/kernel/diagram'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'

const diagramJson = JSON.stringify({
  root: 'r0',
  regions: { r0: { kind: 'sheet' } },
  nodes: {},
  wires: {},
})

function treeWire(treeId: string, diagramKey: number) {
  return { treeId, diagramKey, x: 0, z: 0, yaw: 0 }
}

function openingOrders(blank: Record<string, unknown> = {
  orderId: 'blank-sprout', state: 'pending', pot: null,
}): readonly unknown[] {
  return openingOrderCatalog.current.definitions.map((definition) =>
    definition.id === 'blank-sprout'
      ? blank
      : { orderId: definition.id, state: 'pending', pot: null },
  )
}

function slotWire(overrides: Record<string, unknown> = {}) {
  return {
    slotId: 'large-1',
    displayName: 'Large Tree',
    updatedAtMs: 0,
    camera: { x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 },
    trees: [treeWire('a', 7)],
    diagrams: [{ diagramKey: 7, diagramJson }],
    reputation: 0,
    orders: openingOrders(),
    tutorialsEnabled: true,
    completedTutorialMilestones: ['move'],
    acquiredToolIds: ['sprout-spawner'],
    ...overrides,
  }
}

describe('loaded game slot decoding', () => {
  it('owns canonical diagram content independently of caller and consumer mutations', () => {
    const snapshot = snapshotFromJson(`${diagramJson}\n`)
    expect(snapshot.json).toBe(JSON.stringify(diagramToJson(snapshot.diagram)))
    expect(snapshotFromDiagram(snapshot.diagram)).toEqual(snapshot)

    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const callerDiagram = builder.build()
    const owned = snapshotFromDiagram(callerDiagram)
    ;(callerDiagram.regions[cut] as { kind: 'cut'; parent: string }).parent = 'caller-forgery'
    expect(callerDiagram.regions[cut]).toEqual({ kind: 'cut', parent: 'caller-forgery' })
    expect(owned.diagram.regions[cut]).toEqual({ kind: 'cut', parent: builder.root })

    try {
      ;(owned.diagram.regions[cut] as { kind: 'cut'; parent: string }).parent = 'consumer-forgery'
    } catch {}
    expect(owned.diagram.regions[cut]).toEqual({ kind: 'cut', parent: builder.root })
    expect(owned.json).toBe(JSON.stringify(diagramToJson(owned.diagram)))
  })

  it('decodes equivalent diagrams and gives every tree the generic model', () => {
    const loaded = decodeLoadedSlot(slotWire({ trees: [treeWire('a', 7), treeWire('b', 7)] }))

    expect(loaded.trees.size).toBe(2)
    expect(loaded.trees.get('a')!.snapshot).toEqual(loaded.trees.get('b')!.snapshot)
    expect(loaded.trees.get('a')!.snapshot.json).toBe(diagramJson)
    expect(loaded.trees.get('a')!.placement).toEqual({ x: 0, z: 0, yaw: 0 })
    expect(loaded).toMatchObject({
      slot: { id: 'large-1', name: 'Large Tree', updatedAtMs: 0 },
      camera: { position: { x: 0, y: 1.7, z: 82 }, yaw: 0, pitch: -0.04 },
    })
    expect(loaded.progress).toEqual({
      reputation: 0,
      orders: new Map(openingOrderCatalog.current.definitions.map((definition) => [
        definition.id, { kind: 'pending' },
      ])),
      tutorialsEnabled: true,
      completedTutorialMilestones: new Set(['move']),
      acquiredToolIds: new Set(['sprout-spawner']),
    })
  })

  it('rejects missing diagram references and malformed kernel diagrams', () => {
    expect(() => decodeLoadedSlot(slotWire({ trees: [treeWire('a', 99)] })))
      .toThrow("tree 'a' references missing diagram key 99")
    expect(() => decodeLoadedSlot(slotWire({
      diagrams: [{ diagramKey: 7, diagramJson: '{}' }],
    }))).toThrow(/diagram 0: malformed diagram JSON/)
  })

  it('rejects duplicate keys, duplicate tree ids, and non-finite coordinates', () => {
    expect(() => decodeLoadedSlot(slotWire({
      diagrams: [
        { diagramKey: 7, diagramJson },
        { diagramKey: 7, diagramJson: `${diagramJson} ` },
      ],
    }))).toThrow('duplicate diagram key 7')
    expect(() => decodeLoadedSlot(slotWire({
      trees: [treeWire('a', 7), treeWire('a', 7)],
    }))).toThrow("duplicate tree id 'a'")
    expect(() => decodeLoadedSlot(slotWire({
      camera: { x: 0, y: Number.NaN, z: 82, yaw: 0, pitch: -0.04 },
    }))).toThrow('camera.y must be a finite number')
  })

  it('rejects values outside the exact loaded-slot wire shape', () => {
    expect(() => decodeLoadedSlot(null)).toThrow('loaded slot must be an object')
    expect(() => decodeLoadedSlot(slotWire({ updatedAtMs: 1.5 })))
      .toThrow('loaded slot.updatedAtMs must be a safe integer')
    expect(() => decodeLoadedSlot(slotWire({ trees: 'not an array' })))
      .toThrow('loaded slot.trees must be an array')
    expect(() => decodeLoadedSlot(slotWire({ unexpected: true })))
      .toThrow("loaded slot has unknown field 'unexpected'")
  })

  it('strictly decodes tutorial progression IDs and enabled state', () => {
    expect(() => decodeLoadedSlot(slotWire({ tutorialsEnabled: 'true' })))
      .toThrow('loaded slot.tutorialsEnabled must be a boolean')
    expect(() => decodeLoadedSlot(slotWire({ completedTutorialMilestones: ['move', 'move'] })))
      .toThrow("duplicate completed tutorial milestone id 'move'")
    expect(() => decodeLoadedSlot(slotWire({ completedTutorialMilestones: [''] })))
      .toThrow('completed tutorial milestone id must be a non-blank string')
    expect(() => decodeLoadedSlot(slotWire({ acquiredToolIds: ['sprout-spawner', 'sprout-spawner'] })))
      .toThrow("duplicate acquired tool id 'sprout-spawner'")
    expect(() => decodeLoadedSlot(slotWire({ acquiredToolIds: ['  '] })))
      .toThrow('acquired tool id must be a non-blank string')
  })

  it('validates loaded orders against the supplied live catalog revision', () => {
    const definitions = openingOrderCatalog.current.definitions.slice(0, -1)
    const catalog: OrderCatalogRevision = {
      definitions,
      byId: new Map(definitions.map((definition) => [definition.id, definition])),
    }

    expect(() => decodeLoadedSlot(slotWire({ orders: openingOrders().slice(0, -1) }), catalog))
      .not.toThrow()
    expect(() => decodeLoadedSlot(slotWire(), catalog))
      .toThrow('loaded slot.orders must match the authored order catalog')
  })

  it('rejects any saved order set that differs from the authored catalog', () => {
    expect(() => decodeLoadedSlot(slotWire({ orders: [] })))
      .toThrow('loaded slot.orders must match the authored order catalog')
    expect(() => decodeLoadedSlot(slotWire({
      orders: [{ orderId: 'not-authored', state: 'pending', pot: null }],
    }))).toThrow('loaded slot.orders must match the authored order catalog')
  })

  it('rejects invalid order reputation and state-specific wire data', () => {
    expect(() => decodeLoadedSlot(slotWire({ reputation: -1 })))
      .toThrow('loaded slot.reputation must be a nonnegative safe integer')
    expect(() => decodeLoadedSlot(slotWire({ reputation: Number.MAX_SAFE_INTEGER + 1 })))
      .toThrow('loaded slot.reputation must be a nonnegative safe integer')
    expect(() => decodeLoadedSlot(slotWire({
      orders: openingOrders({ orderId: 'blank-sprout', state: 'accepted', pot: null }),
    }))).toThrow("order 'blank-sprout'.pot must be an object")
    expect(() => decodeLoadedSlot(slotWire({
      orders: openingOrders({
        orderId: 'blank-sprout', state: 'accepted',
        pot: { x: Number.NaN, z: -4, yaw: 0.25 },
      }),
    }))).toThrow("order 'blank-sprout'.pot.x must be a finite number")
    expect(() => decodeLoadedSlot(slotWire({
      orders: openingOrders({ orderId: 'blank-sprout', state: 'pending', pot: { x: 2, z: -4, yaw: 0.25 } }),
    }))).toThrow("order 'blank-sprout' pending state requires a null pot")
    expect(() => decodeLoadedSlot(slotWire({
      orders: openingOrders({ orderId: 'blank-sprout', state: 'completed', pot: { x: 2, z: -4, yaw: 0.25 } }),
    }))).toThrow("order 'blank-sprout' completed state requires a null pot")
    expect(() => decodeLoadedSlot(slotWire({
      orders: openingOrders({ orderId: 'blank-sprout', state: 'pending', pot: null, reward: 1 }),
    }))).toThrow("order has unknown field 'reward'")
  })

  it('decodes an accepted saved order with its finite pot placement', () => {
    const world = decodeLoadedSlot(slotWire({
      orders: openingOrders({
        orderId: 'blank-sprout', state: 'accepted',
        pot: { x: 2, z: -4, yaw: 0.25 },
      }),
    }))

    expect(world.progress.orders.get('blank-sprout')).toEqual({
      kind: 'accepted', pot: { x: 2, z: -4, yaw: 0.25 },
    })
  })
})

describe('save slot list decoding', () => {
  it('strictly decodes the slot returned by create before it can be loaded', () => {
    expect(decodeCreatedSlot({
      slotId: 'created', displayName: 'New orchard', updatedAtMs: 12, error: null,
    })).toEqual({
      slotId: 'created', displayName: 'New orchard', updatedAtMs: 12, error: null,
    })
    expect(() => decodeCreatedSlot({
      slotId: 3, displayName: 'Bad', updatedAtMs: 12, error: null,
    })).toThrow('created slot.slotId must be a string')
  })

  it('keeps valid and invalid ordinary slots visible to the start menu', () => {
    expect(decodeSlotList([
      { slotId: 'good', displayName: 'Good', updatedAtMs: 12, error: null },
      { slotId: 'bad', displayName: 'Bad', updatedAtMs: 0, error: 'invalid structure' },
    ])).toEqual([
      { slotId: 'good', displayName: 'Good', updatedAtMs: 12, error: null },
      { slotId: 'bad', displayName: 'Bad', updatedAtMs: 0, error: 'invalid structure' },
    ])
  })

  it('rejects duplicate slot ids and malformed list entries', () => {
    expect(() => decodeSlotList([
      { slotId: 'same', displayName: 'One', updatedAtMs: 1, error: null },
      { slotId: 'same', displayName: 'Two', updatedAtMs: 2, error: null },
    ])).toThrow("duplicate slot id 'same'")
    expect(() => decodeSlotList([
      { slotId: 'bad', displayName: 'Bad', updatedAtMs: Number.NaN, error: null },
    ])).toThrow('slot 0.updatedAtMs must be a safe integer')
  })
})
