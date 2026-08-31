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
  save(definitions: readonly SerializedOrderDefinition[]): Promise<void>
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

export const orderContentClient: OrderContentClient = {
  save: (definitions) => invoke('save_order_catalog', { content: definitions })
    .then(decodeSavedOrderCatalog),
}
