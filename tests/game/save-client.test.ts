import { describe, expect, it } from 'vitest'
import {
  createSaveClient,
  httpSaveTransport,
  type CameraRecord,
  type SaveOperation,
  type SaveTransport,
  type TreeUpdate,
} from '../../src/game/save-client'

const diagramJson = JSON.stringify({
  root: 'r0',
  regions: { r0: { kind: 'sheet' } },
  nodes: {},
  wires: {},
})

const camera: CameraRecord = { x: 1, y: 1.7, z: 8, yaw: 0.2, pitch: -0.18 }
const tree: TreeUpdate = { treeId: 'tree-a', diagramJson, x: 3, z: 4, yaw: 0.6 }

const loadedSlot = {
  slotId: 'slot-a',
  displayName: 'First orchard',
  updatedAtMs: 24,
  camera,
  trees: [{ treeId: 'tree-a', diagramKey: 7, x: 3, z: 4, yaw: 0.6 }],
  diagrams: [{ diagramKey: 7, diagramJson }],
}

type RecordedRequest = {
  readonly operation: SaveOperation
  readonly input: Record<string, unknown>
}

describe('save client transports', () => {
  // This fails if a public SaveClient method bypasses its selected transport.
  it('maps every SaveClient operation through one selected transport', async () => {
    const requests: RecordedRequest[] = []
    const transport: SaveTransport = {
      async request(operation, input) {
        requests.push({ operation, input })
        switch (operation) {
          case 'list': return [{ slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null }]
          case 'create': return { slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null }
          case 'load': return loadedSlot
          case 'update-tree': return 9
          case 'update-camera': return null
        }
      },
    }
    const client = createSaveClient(transport)

    await expect(client.list()).resolves.toEqual([
      { slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null },
    ])
    await expect(client.create('Second orchard', camera, [tree])).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    const world = await client.load('slot-a')
    expect(world.slot).toEqual({ id: 'slot-a', name: 'First orchard', updatedAtMs: 24 })
    expect(world.camera).toEqual({ position: { x: 1, y: 1.7, z: 8 }, yaw: 0.2, pitch: -0.18 })
    expect(world.trees.get('tree-a')?.placement).toEqual({ x: 3, z: 4, yaw: 0.6 })
    await expect(client.updateTree('slot-a', tree)).resolves.toBe(9)
    await expect(client.updateCamera('slot-a', camera)).resolves.toBeUndefined()

    expect(requests).toEqual([
      { operation: 'list', input: {} },
      { operation: 'create', input: { displayName: 'Second orchard', camera, trees: [tree] } },
      { operation: 'load', input: { slotId: 'slot-a' } },
      { operation: 'update-tree', input: { slotId: 'slot-a', update: tree } },
      { operation: 'update-camera', input: { slotId: 'slot-a', camera } },
    ])
  })

  // This fails if an HTTP error is swallowed or another transport is attempted.
  it('HTTP transport rejects a failed response without trying another transport', async () => {
    const requests: RequestInit[] = []
    const fetch: typeof globalThis.fetch = async (_url, init) => {
      requests.push(init ?? {})
      return new Response('save failed', { status: 500 })
    }
    const client = createSaveClient(httpSaveTransport({
      baseUrl: 'http://127.0.0.1:1421',
      token: 'test-token',
      fetch,
    }))

    await expect(client.list()).rejects.toThrow('save failed')
    expect(requests).toHaveLength(1)
  })
})
