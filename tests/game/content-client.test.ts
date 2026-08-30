import { describe, expect, it } from 'vitest'
import {
  createAuthoredContentClient,
  httpAuthoredContentTransport,
  type AuthoredContentTransport,
} from '../../src/game/content-client'
import type { TutorialContentDefinition } from '../../src/game/tutorial/content'
import type { ToolContentDefinition } from '../../src/game/tools/content'

const tutorial: readonly TutorialContentDefinition[] = [{
  milestoneId: 'move',
  text: 'Move with W/A/S/D.',
}]
const tools: readonly ToolContentDefinition[] = [{
  id: 'sprout-spawner',
  name: 'Sprout Spawner',
  description: 'Plant a blank sprout.',
}]

describe('authored content client', () => {
  // This catches adding a save identity or sending either document under the wrong operation.
  it('sends tutorial and tool copy as slot-independent content operations', async () => {
    const requests: Array<{ operation: string; input: Record<string, unknown> }> = []
    const transport: AuthoredContentTransport = {
      async request(operation, input) {
        requests.push({ operation, input })
        return null
      },
    }
    const client = createAuthoredContentClient(transport)

    await client.saveTutorial(tutorial)
    await client.saveTools(tools)

    expect(requests).toEqual([
      { operation: 'save-tutorial', input: { content: tutorial } },
      { operation: 'save-tools', input: { content: tools } },
    ])
  })

  // This catches a permissive success decoder hiding a malformed native or HTTP response.
  it('accepts only null save responses', async () => {
    const client = createAuthoredContentClient({
      request: async () => ({ saved: true }),
    })

    await expect(client.saveTutorial(tutorial))
      .rejects.toThrow('saved authored content response must be null')
  })

  // This catches route aliasing between the tutorial and tool permanent authorities.
  it('posts each document to its distinct authenticated playtest route', async () => {
    const requests: Array<{ url: string; init: RequestInit }> = []
    const fetch: typeof globalThis.fetch = async (url, init) => {
      requests.push({ url: String(url), init: init ?? {} })
      return new Response('null', {
        status: 200,
        headers: { 'content-type': 'application/json' },
      })
    }
    const client = createAuthoredContentClient(httpAuthoredContentTransport({
      baseUrl: 'http://127.0.0.1:1421/',
      token: 'test-token',
      fetch,
    }))

    await client.saveTutorial(tutorial)
    await client.saveTools(tools)

    expect(requests.map(({ url, init }) => ({
      url,
      method: init.method,
      headers: Object.fromEntries(new Headers(init.headers).entries()),
      body: init.body,
    }))).toEqual([
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/content/tutorial',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: JSON.stringify({ content: tutorial }),
      },
      {
        url: 'http://127.0.0.1:1421/__orchard_playtest/content/tools',
        method: 'POST',
        headers: { 'content-type': 'application/json', 'x-orchard-playtest-token': 'test-token' },
        body: JSON.stringify({ content: tools }),
      },
    ])
  })

  // This catches a failed durable write being swallowed or retried by the client.
  it('propagates the single persistent-write failure', async () => {
    const failure = new Error('content destination is read-only')
    let calls = 0
    const client = createAuthoredContentClient({
      async request() {
        calls += 1
        throw failure
      },
    })

    await expect(client.saveTools(tools)).rejects.toBe(failure)
    expect(calls).toBe(1)
  })
})
