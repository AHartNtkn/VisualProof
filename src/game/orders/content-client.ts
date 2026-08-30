import { invoke } from '@tauri-apps/api/core'
import { diagramToJson } from '../../kernel/diagram'
import type { OrderCatalogRevision } from './catalog'

export type SerializedOrderDefinition = {
  readonly id: string
  readonly prerequisites: readonly string[]
  readonly reward: number
  readonly goal: unknown
  readonly formula?: string
}

export type OrderContentClient = {
  save(slotId: string, definitions: readonly SerializedOrderDefinition[]): Promise<void>
}

export type OrderContentOperation = 'save'

export type OrderContentTransport = {
  request(operation: OrderContentOperation, input: Record<string, unknown>): Promise<unknown>
}

export function serializeOrderCatalog(
  revision: OrderCatalogRevision,
): readonly SerializedOrderDefinition[] {
  return revision.definitions.map((definition) => definition.formula === undefined
    ? {
      id: definition.id,
      prerequisites: [...definition.prerequisites],
      reward: definition.reward,
      goal: diagramToJson(definition.goal.diagram),
    }
    : {
      id: definition.id,
      prerequisites: [...definition.prerequisites],
      reward: definition.reward,
      goal: diagramToJson(definition.goal.diagram),
      formula: definition.formula,
    })
}

function decodeSavedOrderCatalog(value: unknown): void {
  if (value !== null) throw new Error('saved order catalog response must be null')
}

export function createOrderContentClient(transport: OrderContentTransport): OrderContentClient {
  return {
    save: (slotId, definitions) => transport.request('save', { slotId, content: definitions })
      .then(decodeSavedOrderCatalog),
  }
}

export const tauriOrderContentTransport: OrderContentTransport = {
  request(_operation, input) {
    return invoke('save_order_catalog', input)
  },
}

export function httpOrderContentTransport(config: {
  baseUrl: string
  token: string
  fetch: typeof globalThis.fetch
}): OrderContentTransport {
  const baseUrl = config.baseUrl.replace(/\/$/, '')
  return {
    async request(_operation, input): Promise<unknown> {
      let response: Response
      try {
        response = await config.fetch.call(
          globalThis,
          `${baseUrl}/__orchard_playtest/content/orders`,
          {
            method: 'POST',
            headers: {
              'content-type': 'application/json',
              'x-orchard-playtest-token': config.token,
            },
            body: JSON.stringify(input),
          },
        )
      } catch (error) {
        const detail = error instanceof Error ? error.message : String(error)
        throw new Error(`browser playtest content service unavailable: ${detail}`)
      }
      if (!response.ok) throw new Error(await response.text())
      return response.json()
    },
  }
}

export function selectOrderContentTransport(config: {
  transportName: string
  baseUrl?: string
  token?: string
  fetch: typeof globalThis.fetch
}): OrderContentTransport {
  switch (config.transportName) {
    case 'tauri': return tauriOrderContentTransport
    case 'playtest-http': {
      const { baseUrl, token } = config
      if (baseUrl === undefined || baseUrl.trim().length === 0
        || token === undefined || token.trim().length === 0) {
        throw new Error(
          'playtest HTTP content transport requires VITE_ORCHARD_PLAYTEST_URL and VITE_ORCHARD_PLAYTEST_TOKEN',
        )
      }
      return httpOrderContentTransport({ baseUrl, token, fetch: config.fetch })
    }
    default: throw new Error(`unsupported Orchard content transport '${config.transportName}'`)
  }
}

export const orderContentClient = createOrderContentClient(selectOrderContentTransport({
  transportName: import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri',
  baseUrl: import.meta.env.VITE_ORCHARD_PLAYTEST_URL,
  token: import.meta.env.VITE_ORCHARD_PLAYTEST_TOKEN,
  fetch: globalThis.fetch,
}))
