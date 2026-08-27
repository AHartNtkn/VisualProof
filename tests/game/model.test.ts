import { describe, expect, it } from 'vitest'
import { decodeLoadedSlot } from '../../src/game/model'
import { decodeCreatedSlot, decodeSlotList } from '../../src/game/save-client'

const diagramJson = JSON.stringify({
  root: 'r0',
  regions: { r0: { kind: 'sheet' } },
  nodes: {},
  wires: {},
})

function treeWire(treeId: string, diagramKey: number) {
  return { treeId, diagramKey, x: 0, z: 0, yaw: 0 }
}

function slotWire(overrides: Record<string, unknown> = {}) {
  return {
    slotId: 'large-1',
    displayName: 'Large Tree',
    updatedAtMs: 0,
    camera: { x: 0, y: 1.7, z: 82, yaw: 0, pitch: -0.04 },
    trees: [treeWire('a', 7)],
    diagrams: [{ diagramKey: 7, diagramJson }],
    ...overrides,
  }
}

describe('loaded game slot decoding', () => {
  it('decodes equivalent diagrams and gives every tree the generic model', () => {
    const loaded = decodeLoadedSlot(slotWire({ trees: [treeWire('a', 7), treeWire('b', 7)] }))

    expect(loaded.trees.size).toBe(2)
    expect(loaded.trees.get('a')!.diagram).toEqual(loaded.trees.get('b')!.diagram)
    expect(loaded.trees.get('a')!.diagramJson).toBe(diagramJson)
    expect(loaded.trees.get('a')!.placement).toEqual({ x: 0, z: 0, yaw: 0 })
    expect(loaded).toMatchObject({
      slot: { id: 'large-1', name: 'Large Tree', updatedAtMs: 0 },
      camera: { position: { x: 0, y: 1.7, z: 82 }, yaw: 0, pitch: -0.04 },
    })
  })

  it('rejects missing diagram references and malformed kernel diagrams', () => {
    expect(() => decodeLoadedSlot(slotWire({ trees: [treeWire('a', 99)] })))
      .toThrow("tree 'a' references missing diagram key 99")
    expect(() => decodeLoadedSlot(slotWire({
      diagrams: [{ diagramKey: 7, diagramJson: '{}' }],
    }))).toThrow(/malformed diagram JSON/)
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
