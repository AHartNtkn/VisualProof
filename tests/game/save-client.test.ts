import { describe, expect, it } from 'vitest'
import {
  createSaveClient,
  httpSaveTransport,
  orderRecordsFromProgress,
  selectSaveTransport,
  type CameraRecord,
  type CreateSlotState,
  type OrderRecordWire,
  type SaveOperation,
  type SaveTransport,
  type TreeUpdate,
} from '../../src/game/save-client'
import type { OrderProgress } from '../../src/game/orders/catalog'

const diagramJson = '{"root":"r0","regions":{"r0":{"kind":"sheet"}},"nodes":{},"wires":{}}'

const camera: CameraRecord = { x: 1, y: 1.7, z: 8, yaw: 0.2, pitch: -0.18 }
const tree: TreeUpdate = { treeId: 'tree-a', diagramJson, x: 3, z: 4, yaw: 0.6 }
const initialOrders: readonly OrderRecordWire[] = [
  { orderId: 'starter-double-cut', state: 'pending', pot: null },
]
const createState: CreateSlotState = {
  displayName: 'Second orchard', camera, trees: [tree], reputation: 0, orders: initialOrders,
}

const loadedSlot = {
  slotId: 'slot-a',
  displayName: 'First orchard',
  updatedAtMs: 24,
  camera,
  trees: [{ treeId: 'tree-a', diagramKey: 7, x: 3, z: 4, yaw: 0.6 }],
  diagrams: [{ diagramKey: 7, diagramJson }],
  reputation: 0,
  orders: initialOrders,
}

type RecordedRequest = {
  readonly operation: SaveOperation
  readonly input: Record<string, unknown>
}

type RecordedHttpRequest = {
  readonly url: string
  readonly init: RequestInit
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
          case 'insert-tree': return 10
          case 'update-camera': return null
          case 'accept-order': return null
          case 'abandon-order': return null
          case 'complete-order': return 1
        }
      },
    }
    const client = createSaveClient(transport)

    await expect(client.list()).resolves.toEqual([
      { slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null },
    ])
    await expect(client.create(createState)).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    const world = await client.load('slot-a')
    expect(world.slot).toEqual({ id: 'slot-a', name: 'First orchard', updatedAtMs: 24 })
    expect(world.camera).toEqual({ position: { x: 1, y: 1.7, z: 8 }, yaw: 0.2, pitch: -0.18 })
    expect(world.trees.get('tree-a')?.placement).toEqual({ x: 3, z: 4, yaw: 0.6 })
    await expect(client.updateTree('slot-a', tree)).resolves.toBe(9)
    await expect(client.insertTree('slot-a', tree)).resolves.toBe(10)
    await expect(client.updateCamera('slot-a', camera)).resolves.toBeUndefined()
    await expect(client.acceptOrder('slot-a', 'starter-double-cut', { x: 2, z: -4, yaw: 0.25 }))
      .resolves.toBeUndefined()
    await expect(client.abandonOrder('slot-a', 'starter-double-cut')).resolves.toBeUndefined()
    await expect(client.completeOrder('slot-a', 'starter-double-cut', 1)).resolves.toBe(1)

    expect(requests).toEqual([
      { operation: 'list', input: {} },
      { operation: 'create', input: createState },
      { operation: 'load', input: { slotId: 'slot-a' } },
      { operation: 'update-tree', input: { slotId: 'slot-a', update: tree } },
      { operation: 'insert-tree', input: { slotId: 'slot-a', update: tree } },
      { operation: 'update-camera', input: { slotId: 'slot-a', camera } },
      { operation: 'accept-order', input: { slotId: 'slot-a', orderId: 'starter-double-cut', pot: { x: 2, z: -4, yaw: 0.25 } } },
      { operation: 'abandon-order', input: { slotId: 'slot-a', orderId: 'starter-double-cut' } },
      { operation: 'complete-order', input: { slotId: 'slot-a', orderId: 'starter-double-cut', reward: 1 } },
    ])
  })

  // This fails if creation sends any order set other than the authored catalog.
  it('rejects creation progress with a non-catalog order set before transport', async () => {
    const transport: SaveTransport = { request: async () => { throw new Error('transport was called') } }
    const client = createSaveClient(transport)
    const progress: OrderProgress = {
      reputation: 0,
      orders: new Map([['unknown-order', { kind: 'pending' }]]),
    }

    expect(() => orderRecordsFromProgress(progress)).toThrow('progress orders must match the authored order catalog')
    await expect(client.create({ ...createState, orders: [{ orderId: 'unknown-order', state: 'pending', pot: null }] }))
      .rejects.toThrow('create state orders must match the authored order catalog')
  })

  it('emits order records in authored order with state-specific pots', () => {
    const progress: OrderProgress = {
      reputation: 3,
      orders: new Map([['starter-double-cut', { kind: 'completed' }]]),
    }

    expect(orderRecordsFromProgress(progress)).toEqual([
      { orderId: 'starter-double-cut', state: 'completed', pot: null },
    ])
  })

  // This fails if a Rust operation response reaches game state without matching its wire type.
  it('rejects malformed order-operation and revision responses', async () => {
    const transport: SaveTransport = {
      async request(operation) {
        switch (operation) {
          case 'insert-tree': return 'not a revision'
          case 'accept-order': return { accepted: true }
          case 'complete-order': return Number.NaN
          default: throw new Error(`unexpected operation ${operation}`)
        }
      },
    }
    const client = createSaveClient(transport)

    await expect(client.insertTree('slot-a', tree)).rejects.toThrow('inserted tree revision must be a safe integer')
    await expect(client.acceptOrder('slot-a', 'starter-double-cut', { x: 2, z: -4, yaw: 0.25 }))
      .rejects.toThrow('accepted order response must be null')
    await expect(client.completeOrder('slot-a', 'starter-double-cut', 1))
      .rejects.toThrow('completed order reputation must be a safe integer')
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

  // This fails if a network failure leaks a browser-specific fetch error or triggers another request.
  it('HTTP transport reports an unavailable playtest save service after one rejected fetch', async () => {
    let requestCount = 0
    const fetch: typeof globalThis.fetch = async () => {
      requestCount += 1
      throw new TypeError('Failed to fetch')
    }
    const client = createSaveClient(httpSaveTransport({
      baseUrl: 'http://127.0.0.1:1421',
      token: 'test-token',
      fetch,
    }))

    await expect(client.list()).rejects.toThrow(
      'browser playtest save service unavailable: Failed to fetch',
    )
    expect(requestCount).toBe(1)
  })

  // This fails if a defined-but-empty service setting is accepted as complete configuration.
  it.each([
    { baseUrl: '', token: 'test-token' },
    { baseUrl: '   ', token: 'test-token' },
    { baseUrl: 'http://127.0.0.1:1421', token: '' },
    { baseUrl: 'http://127.0.0.1:1421', token: '\t  ' },
  ])('rejects incomplete playtest HTTP configuration: %o', ({ baseUrl, token }) => {
    expect(() => selectSaveTransport({
      transportName: 'playtest-http',
      baseUrl,
      token,
      fetch: globalThis.fetch,
    })).toThrow(
      'playtest HTTP save transport requires VITE_ORCHARD_PLAYTEST_URL and VITE_ORCHARD_PLAYTEST_TOKEN',
    )
  })

  // This fails if a browser-native fetch is invoked with the transport config as its receiver.
  it('HTTP transport invokes browser-native fetch with globalThis as its receiver', async () => {
    const fetch: typeof globalThis.fetch = function (
      this: typeof globalThis,
      _url: RequestInfo | URL,
      _init?: RequestInit,
    ): Promise<Response> {
      if (this !== globalThis) throw new TypeError("Failed to execute 'fetch' on 'Window': Illegal invocation")
      return Promise.resolve(new Response('[]', {
        status: 200,
        headers: { 'content-type': 'application/json' },
      }))
    }
    const client = createSaveClient(httpSaveTransport({
      baseUrl: 'http://127.0.0.1:1421',
      token: 'test-token',
      fetch,
    }))

    await expect(client.list()).resolves.toEqual([])
  })

  // This fails if a route, token header, JSON envelope, or decoded HTTP response drifts.
  it('HTTP transport sends every SaveClient operation using the Task 1 wire contract', async () => {
    const requests: RecordedHttpRequest[] = []
    const fetch: typeof globalThis.fetch = async (url, init) => {
      const request = { url: String(url), init: init ?? {} }
      requests.push(request)
      const responses: Record<string, unknown> = {
        '/__orchard_playtest/save/list': [
          { slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null },
        ],
        '/__orchard_playtest/save/create': {
          slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
        },
        '/__orchard_playtest/save/load': loadedSlot,
        '/__orchard_playtest/save/update-tree': 9,
        '/__orchard_playtest/save/insert-tree': 10,
        '/__orchard_playtest/save/update-camera': null,
        '/__orchard_playtest/save/accept-order': null,
        '/__orchard_playtest/save/abandon-order': null,
        '/__orchard_playtest/save/complete-order': 1,
      }
      return new Response(JSON.stringify(responses[new URL(request.url).pathname]), {
        status: 200,
        headers: { 'content-type': 'application/json' },
      })
    }
    const client = createSaveClient(httpSaveTransport({
      baseUrl: 'http://127.0.0.1:1421',
      token: 'test-token',
      fetch,
    }))

    await expect(client.list()).resolves.toEqual([
      { slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null },
    ])
    await expect(client.create(createState)).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    const world = await client.load('slot-a')
    expect(world.slot).toEqual({ id: 'slot-a', name: 'First orchard', updatedAtMs: 24 })
    expect(world.camera).toEqual({ position: { x: 1, y: 1.7, z: 8 }, yaw: 0.2, pitch: -0.18 })
    expect(world.trees.get('tree-a')?.placement).toEqual({ x: 3, z: 4, yaw: 0.6 })
    await expect(client.updateTree('slot-a', tree)).resolves.toBe(9)
    await expect(client.insertTree('slot-a', tree)).resolves.toBe(10)
    await expect(client.updateCamera('slot-a', camera)).resolves.toBeUndefined()
    await expect(client.acceptOrder('slot-a', 'starter-double-cut', { x: 2, z: -4, yaw: 0.25 }))
      .resolves.toBeUndefined()
    await expect(client.abandonOrder('slot-a', 'starter-double-cut')).resolves.toBeUndefined()
    await expect(client.completeOrder('slot-a', 'starter-double-cut', 1)).resolves.toBe(1)

    expect(requests.map(({ url, init }) => ({
      url,
      method: init.method,
      headers: Object.fromEntries(new Headers(init.headers).entries()),
      body: init.body,
    }))).toEqual([
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/list',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/create',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"displayName":"Second orchard","camera":{"x":1,"y":1.7,"z":8,"yaw":0.2,"pitch":-0.18},"trees":[{"treeId":"tree-a","diagramJson":"{\\"root\\":\\"r0\\",\\"regions\\":{\\"r0\\":{\\"kind\\":\\"sheet\\"}},\\"nodes\\":{},\\"wires\\":{}}","x":3,"z":4,"yaw":0.6}],"reputation":0,"orders":[{"orderId":"starter-double-cut","state":"pending","pot":null}]}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/load',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a"}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/update-tree',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","update":{"treeId":"tree-a","diagramJson":"{\\"root\\":\\"r0\\",\\"regions\\":{\\"r0\\":{\\"kind\\":\\"sheet\\"}},\\"nodes\\":{},\\"wires\\":{}}","x":3,"z":4,"yaw":0.6}}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/insert-tree',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","update":{"treeId":"tree-a","diagramJson":"{\\"root\\":\\"r0\\",\\"regions\\":{\\"r0\\":{\\"kind\\":\\"sheet\\"}},\\"nodes\\":{},\\"wires\\":{}}","x":3,"z":4,"yaw":0.6}}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/update-camera',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","camera":{"x":1,"y":1.7,"z":8,"yaw":0.2,"pitch":-0.18}}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/accept-order',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","orderId":"starter-double-cut","pot":{"x":2,"z":-4,"yaw":0.25}}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/abandon-order',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","orderId":"starter-double-cut"}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/complete-order',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","orderId":"starter-double-cut","reward":1}',
      },
    ])
  })
})
