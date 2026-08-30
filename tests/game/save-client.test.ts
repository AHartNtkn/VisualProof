import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import {
  createSaveClient,
  httpSaveTransport,
  initialOrderCreateState,
  orderRecordsFromProgress,
  selectSaveTransport,
  type CameraRecord,
  type CreateSlotState,
  type OrderRecordWire,
  type SaveOperation,
  type SaveTransport,
  type TreeUpdate,
} from '../../src/game/save-client'
import {
  LiveOrderCatalog,
  decodeOrderCatalog,
  openingOrderCatalog,
  type OrderProgress,
} from '../../src/game/orders/catalog'
import { initialOrderProgress } from '../../src/game/orders/session'

const diagramJson = '{"root":"r0","regions":{"r0":{"kind":"sheet"}},"nodes":{},"wires":{}}'
const openingOrderContent: unknown = JSON.parse(readFileSync(
  new URL('../../game/content/orders.json', import.meta.url),
  'utf8',
))

const camera: CameraRecord = { x: 1, y: 1.7, z: 8, yaw: 0.2, pitch: -0.18 }
const tree: TreeUpdate = { treeId: 'tree-a', diagramJson, x: 3, z: 4, yaw: 0.6 }
const openingRevision = openingOrderCatalog.current
const initialOrders: readonly OrderRecordWire[] = orderRecordsFromProgress(
  initialOrderProgress(openingRevision.definitions),
  openingRevision,
)
const createState: CreateSlotState = {
  displayName: 'Second orchard', camera, trees: [tree], reputation: 0, orders: initialOrders,
  tutorialsEnabled: true,
  completedTutorialMilestones: ['move'],
  acquiredToolIds: ['sprout-spawner'],
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
  tutorialsEnabled: true,
  completedTutorialMilestones: ['move'],
  acquiredToolIds: ['sprout-spawner'],
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
          case 'set-tutorials-enabled': return null
          case 'complete-tutorial-milestone': return null
          case 'acquire-tool': return null
        }
      },
    }
    const client = createSaveClient(transport)

    await expect(client.list()).resolves.toEqual([
      { slotId: 'slot-a', displayName: 'First orchard', updatedAtMs: 24, error: null },
    ])
    await expect(client.create(createState, openingRevision)).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    const world = await client.load('slot-a')
    expect(world.slot).toEqual({ id: 'slot-a', name: 'First orchard', updatedAtMs: 24 })
    expect(world.camera).toEqual({ position: { x: 1, y: 1.7, z: 8 }, yaw: 0.2, pitch: -0.18 })
    expect(world.trees.get('tree-a')?.placement).toEqual({ x: 3, z: 4, yaw: 0.6 })
    await expect(client.updateTree('slot-a', tree)).resolves.toBe(9)
    await expect(client.insertTree('slot-a', tree)).resolves.toBe(10)
    await expect(client.updateCamera('slot-a', camera)).resolves.toBeUndefined()
    await expect(client.acceptOrder('slot-a', 'blank-sprout', { x: 2, z: -4, yaw: 0.25 }))
      .resolves.toBeUndefined()
    await expect(client.abandonOrder('slot-a', 'blank-sprout')).resolves.toBeUndefined()
    await expect(client.completeOrder('slot-a', 'blank-sprout', 1)).resolves.toBe(1)
    await expect(client.setTutorialsEnabled('slot-a', false)).resolves.toBeUndefined()
    await expect(client.completeTutorialMilestone('slot-a', 'open-orders')).resolves.toBeUndefined()
    await expect(client.acquireTool('slot-a', 'double-cut')).resolves.toBeUndefined()

    expect(requests).toEqual([
      { operation: 'list', input: {} },
      { operation: 'create', input: createState },
      { operation: 'load', input: { slotId: 'slot-a' } },
      { operation: 'update-tree', input: { slotId: 'slot-a', update: tree } },
      { operation: 'insert-tree', input: { slotId: 'slot-a', update: tree } },
      { operation: 'update-camera', input: { slotId: 'slot-a', camera } },
      { operation: 'accept-order', input: { slotId: 'slot-a', orderId: 'blank-sprout', pot: { x: 2, z: -4, yaw: 0.25 } } },
      { operation: 'abandon-order', input: { slotId: 'slot-a', orderId: 'blank-sprout' } },
      { operation: 'complete-order', input: { slotId: 'slot-a', orderId: 'blank-sprout', reward: 1 } },
      { operation: 'set-tutorials-enabled', input: { slotId: 'slot-a', enabled: false } },
      { operation: 'complete-tutorial-milestone', input: { slotId: 'slot-a', milestoneId: 'open-orders' } },
      { operation: 'acquire-tool', input: { slotId: 'slot-a', toolId: 'double-cut' } },
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

    expect(() => orderRecordsFromProgress(progress, openingRevision)).toThrow('progress orders must match the authored order catalog')
    await expect(client.create(
      { ...createState, orders: [{ orderId: 'unknown-order', state: 'pending', pot: null }] },
      openingRevision,
    ))
      .rejects.toThrow('create state orders must match the authored order catalog')
  })

  // These fail if malformed current-order creation state reaches any selected transport.
  it.each([
    {
      name: 'a negative reputation',
      state: { ...createState, reputation: -1 },
      error: 'create state.reputation must be a nonnegative safe integer',
    },
    {
      name: 'an unsafe reputation',
      state: { ...createState, reputation: Number.MAX_SAFE_INTEGER + 1 },
      error: 'create state.reputation must be a nonnegative safe integer',
    },
    {
      name: 'an accepted order without a pot',
      state: {
        ...createState,
        orders: [{ orderId: 'blank-sprout', state: 'accepted', pot: null }],
      },
      error: "create state order 'blank-sprout' accepted state requires a pot",
    },
    {
      name: 'a pending order with a pot',
      state: {
        ...createState,
        orders: [{ orderId: 'blank-sprout', state: 'pending', pot: { x: 2, z: -4, yaw: 0.25 } }],
      },
      error: "create state order 'blank-sprout' pending state requires a null pot",
    },
    {
      name: 'a non-finite accepted pot coordinate',
      state: {
        ...createState,
        orders: [{ orderId: 'blank-sprout', state: 'accepted', pot: { x: Number.NaN, z: -4, yaw: 0.25 } }],
      },
      error: "create state order 'blank-sprout'.pot.x must be a finite number",
    },
  ])('rejects $name before transport', async ({ state, error }) => {
    let requestCount = 0
    const client = createSaveClient({
      async request() {
        requestCount += 1
        throw new Error('transport was called')
      },
    })

    await expect(client.create(state as unknown as CreateSlotState, openingRevision)).rejects.toThrow(error)
    expect(requestCount).toBe(0)
  })

  it.each([
    {
      name: 'a non-Boolean tutorial setting',
      state: { ...createState, tutorialsEnabled: 'yes' },
      error: 'create state.tutorialsEnabled must be a boolean',
    },
    {
      name: 'a duplicate tutorial milestone',
      state: { ...createState, completedTutorialMilestones: ['move', 'move'] },
      error: "duplicate create state completed tutorial milestone id 'move'",
    },
    {
      name: 'a blank acquired tool ID',
      state: { ...createState, acquiredToolIds: [''] },
      error: 'create state acquired tool id must be a non-blank string',
    },
  ])('rejects $name before transport', async ({ state, error }) => {
    let requestCount = 0
    const client = createSaveClient({
      async request() {
        requestCount += 1
        throw new Error('transport was called')
      },
    })

    await expect(client.create(state as unknown as CreateSlotState, openingRevision)).rejects.toThrow(error)
    expect(requestCount).toBe(0)
  })

  it('emits order records in authored order with state-specific pots', () => {
    const progress: OrderProgress = {
      reputation: 3,
      orders: new Map(openingRevision.definitions.map((definition) => [
        definition.id,
        definition.id === 'blank-sprout' ? { kind: 'completed' as const } : { kind: 'pending' as const },
      ])),
    }

    expect(orderRecordsFromProgress(progress, openingRevision)).toEqual([
      { orderId: 'blank-sprout', state: 'completed', pot: null },
      { orderId: 'single-double-cut', state: 'pending', pot: null },
      { orderId: 'irregular-double-cut-a', state: 'pending', pot: null },
      { orderId: 'irregular-double-cut-b', state: 'pending', pot: null },
    ])
  })

  it('derives new-world records from the revision current at creation time', () => {
    // Catches new-world progress being retained from a catalog revision that has since changed.
    const live = new LiveOrderCatalog(decodeOrderCatalog(openingOrderContent))
    const updatedContent = structuredClone(openingOrderContent) as Array<Record<string, unknown>>
    updatedContent.push({ ...updatedContent[0]!, id: 'new-sprout', prerequisites: [] })
    const updated = decodeOrderCatalog(updatedContent)

    live.publish(updated)

    expect(initialOrderCreateState(live.current).orders.map(({ orderId }) => orderId)).toEqual([
      'blank-sprout',
      'single-double-cut',
      'irregular-double-cut-a',
      'irregular-double-cut-b',
      'new-sprout',
    ])
    expect(initialOrderCreateState(live.current)).toMatchObject({
      tutorialsEnabled: true,
      completedTutorialMilestones: [],
      acquiredToolIds: ['sprout-spawner'],
    })
  })

  it('validates creation against the supplied revision without serializing that revision', async () => {
    const live = new LiveOrderCatalog(decodeOrderCatalog(openingOrderContent))
    const updatedContent = structuredClone(openingOrderContent) as Array<Record<string, unknown>>
    updatedContent.push({ ...updatedContent[0]!, id: 'new-sprout', prerequisites: [] })
    live.publish(decodeOrderCatalog(updatedContent))
    const revision = live.current
    const state: CreateSlotState = {
      ...createState,
      ...initialOrderCreateState(revision),
    }
    const requests: RecordedRequest[] = []
    const client = createSaveClient({
      async request(operation, input) {
        requests.push({ operation, input })
        return { slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null }
      },
    })

    await expect(client.create(state, revision)).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    expect(requests).toEqual([{ operation: 'create', input: state }])
    await expect(client.create(state, openingRevision))
      .rejects.toThrow('create state orders must match the authored order catalog')
  })

  // This fails if a Rust operation response reaches game state without matching its wire type.
  it('rejects malformed order-operation and revision responses', async () => {
    const transport: SaveTransport = {
      async request(operation) {
        switch (operation) {
          case 'insert-tree': return 'not a revision'
          case 'accept-order': return { accepted: true }
          case 'complete-order': return Number.NaN
          case 'set-tutorials-enabled': return { enabled: true }
          default: throw new Error(`unexpected operation ${operation}`)
        }
      },
    }
    const client = createSaveClient(transport)

    await expect(client.insertTree('slot-a', tree)).rejects.toThrow('inserted tree revision must be a safe integer')
    await expect(client.acceptOrder('slot-a', 'blank-sprout', { x: 2, z: -4, yaw: 0.25 }))
      .rejects.toThrow('accepted order response must be null')
    await expect(client.completeOrder('slot-a', 'blank-sprout', 1))
      .rejects.toThrow('completed order reputation must be a nonnegative safe integer')
    await expect(client.setTutorialsEnabled('slot-a', false))
      .rejects.toThrow('set tutorials enabled response must be null')
  })

  // This fails if a negative reputation returned by completion reaches the game.
  it('rejects a negative completed-order reputation response', async () => {
    const client = createSaveClient({
      async request(operation) {
        if (operation === 'complete-order') return -1
        throw new Error(`unexpected operation ${operation}`)
      },
    })

    await expect(client.completeOrder('slot-a', 'blank-sprout', 1))
      .rejects.toThrow('completed order reputation must be a nonnegative safe integer')
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
        '/__orchard_playtest/save/set-tutorials-enabled': null,
        '/__orchard_playtest/save/complete-tutorial-milestone': null,
        '/__orchard_playtest/save/acquire-tool': null,
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
    await expect(client.create(createState, openingRevision)).resolves.toEqual({
      slotId: 'slot-b', displayName: 'Second orchard', updatedAtMs: 25, error: null,
    })
    const world = await client.load('slot-a')
    expect(world.slot).toEqual({ id: 'slot-a', name: 'First orchard', updatedAtMs: 24 })
    expect(world.camera).toEqual({ position: { x: 1, y: 1.7, z: 8 }, yaw: 0.2, pitch: -0.18 })
    expect(world.trees.get('tree-a')?.placement).toEqual({ x: 3, z: 4, yaw: 0.6 })
    await expect(client.updateTree('slot-a', tree)).resolves.toBe(9)
    await expect(client.insertTree('slot-a', tree)).resolves.toBe(10)
    await expect(client.updateCamera('slot-a', camera)).resolves.toBeUndefined()
    await expect(client.acceptOrder('slot-a', 'blank-sprout', { x: 2, z: -4, yaw: 0.25 }))
      .resolves.toBeUndefined()
    await expect(client.abandonOrder('slot-a', 'blank-sprout')).resolves.toBeUndefined()
    await expect(client.completeOrder('slot-a', 'blank-sprout', 1)).resolves.toBe(1)
    await expect(client.setTutorialsEnabled('slot-a', false)).resolves.toBeUndefined()
    await expect(client.completeTutorialMilestone('slot-a', 'open-orders')).resolves.toBeUndefined()
    await expect(client.acquireTool('slot-a', 'double-cut')).resolves.toBeUndefined()

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
        body: JSON.stringify(createState),
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
        body: '{"slotId":"slot-a","orderId":"blank-sprout","pot":{"x":2,"z":-4,"yaw":0.25}}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/abandon-order',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","orderId":"blank-sprout"}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/complete-order',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","orderId":"blank-sprout","reward":1}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/set-tutorials-enabled',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","enabled":false}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/complete-tutorial-milestone',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","milestoneId":"open-orders"}',
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/save/acquire-tool',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: '{"slotId":"slot-a","toolId":"double-cut"}',
      },
    ])
  })
})
