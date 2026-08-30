import { describe, expect, it } from 'vitest'
import {
  createOrderContentClient,
  httpOrderContentTransport,
  serializeOrderCatalog,
  type OrderContentTransport,
  type SerializedOrderDefinition,
} from '../../../src/game/orders/content-client'
import { openingOrderCatalog } from '../../../src/game/orders/catalog'

const serialized: readonly SerializedOrderDefinition[] = [{
  id: 'blank-sprout',
  prerequisites: [],
  reward: 1,
  goal: {
    root: 'r0',
    regions: { r0: { kind: 'sheet' } },
    nodes: {},
    wires: {},
  },
}]

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

  // This catches a wrong operation name, envelope field, or permissive success decoder.
  it('sends the exact save operation and accepts only a null response', async () => {
    const requests: Array<{ operation: string; input: Record<string, unknown> }> = []
    const transport: OrderContentTransport = {
      async request(operation, input) {
        requests.push({ operation, input })
        return null
      },
    }
    const client = createOrderContentClient(transport)

    await expect(client.save('slot-a', serialized)).resolves.toBeUndefined()
    expect(requests).toEqual([{
      operation: 'save',
      input: { slotId: 'slot-a', content: serialized },
    }])

    const malformed = createOrderContentClient({ request: async () => ({ saved: true }) })
    await expect(malformed.save('slot-a', serialized))
      .rejects.toThrow('saved order catalog response must be null')
  })

  // This catches wrapping, swallowing, retrying, or publishing around a backend rejection.
  it('propagates the backend failure from the single save request', async () => {
    const failure = new Error('catalog destination is read-only')
    let calls = 0
    const client = createOrderContentClient({
      async request() {
        calls += 1
        throw failure
      },
    })

    await expect(client.save('slot-a', serialized)).rejects.toBe(failure)
    expect(calls).toBe(1)
  })

  // This catches browser transport drift in route, authentication, or JSON envelope.
  it('posts the content operation to the authenticated playtest route', async () => {
    const requests: Array<{ url: string; init: RequestInit }> = []
    const fetch: typeof globalThis.fetch = async (url, init) => {
      requests.push({ url: String(url), init: init ?? {} })
      return new Response('null', {
        status: 200,
        headers: { 'content-type': 'application/json' },
      })
    }
    const client = createOrderContentClient(httpOrderContentTransport({
      baseUrl: 'http://127.0.0.1:1421/',
      token: 'test-token',
      fetch,
    }))

    await client.save('slot-a', serialized)

    expect(requests.map(({ url, init }) => ({
      url,
      method: init.method,
      headers: Object.fromEntries(new Headers(init.headers).entries()),
      body: init.body,
    }))).toEqual([{
      url: 'http://127.0.0.1:1421/__orchard_playtest/content/orders',
      method: 'POST',
      headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
      body: JSON.stringify({ slotId: 'slot-a', content: serialized }),
    }])
  })

  // This catches HTTP failures being decoded as successful content publication.
  it('rejects a failed playtest response without a retry', async () => {
    let calls = 0
    const client = createOrderContentClient(httpOrderContentTransport({
      baseUrl: 'http://127.0.0.1:1421',
      token: 'test-token',
      fetch: async () => {
        calls += 1
        return new Response('catalog graph contains a cycle', { status: 400 })
      },
    }))

    await expect(client.save('slot-a', serialized))
      .rejects.toThrow('catalog graph contains a cycle')
    expect(calls).toBe(1)
  })
})
