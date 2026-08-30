import openingOrderContent from '../../../game/content/orders.json?raw'
import { diagramFromJson } from '../../kernel/diagram/json'
import { snapshotFromDiagram, type DiagramSnapshot } from '../diagram-snapshot'

export type OrderId = string

export type PotPlacement = {
  readonly x: number
  readonly z: number
  readonly yaw: number
}

export type OrderState =
  | { readonly kind: 'pending' }
  | { readonly kind: 'accepted'; readonly pot: PotPlacement }
  | { readonly kind: 'completed' }

export type OrderProgress = {
  readonly reputation: number
  readonly orders: ReadonlyMap<OrderId, OrderState>
}

export type OrderDefinition = {
  readonly id: OrderId
  readonly prerequisites: readonly OrderId[]
  readonly reward: number
  readonly goal: DiagramSnapshot
  readonly formula?: string
  readonly title: string
  readonly description: string
}

export type OrderCatalogRevision = {
  readonly definitions: readonly OrderDefinition[]
  readonly byId: ReadonlyMap<OrderId, OrderDefinition>
}

export const MAX_REPUTATION = Number.MAX_SAFE_INTEGER
const decodedRevisions = new WeakSet<OrderCatalogRevision>()

function record(value: unknown, what: string): Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error(`${what} must be an object`)
  }
  return value as Record<string, unknown>
}

function exactRecord(value: unknown, keys: readonly string[], what: string): Record<string, unknown> {
  const result = record(value, what)
  for (const key of Object.keys(result)) {
    if (!keys.includes(key)) throw new Error(`${what} has unknown field '${key}'`)
  }
  return result
}

function orderId(value: unknown, what: string): OrderId {
  if (typeof value !== 'string' || value.trim() === '') throw new Error(`${what} must be a non-blank string`)
  return value
}

function prerequisites(value: unknown, what: string): readonly OrderId[] {
  if (!Array.isArray(value)) throw new Error(`${what} must be an array`)
  const seen = new Set<OrderId>()
  const result = value.map((entry, index) => {
    const id = orderId(entry, `${what}[${index}]`)
    if (seen.has(id)) throw new Error(`${what} has duplicate prerequisite '${id}'`)
    seen.add(id)
    return id
  })
  return Object.freeze(result)
}

function reward(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) {
    throw new Error(`${what} must be a nonnegative safe integer`)
  }
  return value
}

function decodeDefinition(value: unknown, index: number): OrderDefinition {
  const raw = exactRecord(value, ['id', 'prerequisites', 'reward', 'goal', 'formula'], `order ${index}`)
  if (!Object.hasOwn(raw, 'id') || !Object.hasOwn(raw, 'prerequisites') || !Object.hasOwn(raw, 'reward') || !Object.hasOwn(raw, 'goal')) {
    throw new Error(`order ${index} must contain id, prerequisites, reward, and goal`)
  }
  if (raw['formula'] !== undefined && typeof raw['formula'] !== 'string') {
    throw new Error(`order ${index}.formula must be a string when present`)
  }
  let goal: DiagramSnapshot
  try {
    goal = snapshotFromDiagram(diagramFromJson(raw['goal']))
  } catch (error) {
    throw new Error(`order ${index}.goal is malformed: ${error instanceof Error ? error.message : String(error)}`)
  }
  const definition: OrderDefinition = raw['formula'] === undefined
    ? {
      id: orderId(raw['id'], `order ${index}.id`),
      prerequisites: prerequisites(raw['prerequisites'], `order ${index}.prerequisites`),
      reward: reward(raw['reward'], `order ${index}.reward`),
      goal,
      title: orderId(raw['id'], `order ${index}.id`),
      description: '',
    }
    : {
      id: orderId(raw['id'], `order ${index}.id`),
      prerequisites: prerequisites(raw['prerequisites'], `order ${index}.prerequisites`),
      reward: reward(raw['reward'], `order ${index}.reward`),
      goal,
      formula: raw['formula'],
      title: orderId(raw['id'], `order ${index}.id`),
      description: raw['formula'],
    }
  return Object.freeze(definition)
}

export function validateOrderCatalog(definitions: readonly OrderDefinition[]): void {
  const byId = new Map<OrderId, OrderDefinition>()
  for (const definition of definitions) {
    if (definition.id.trim() === '') throw new Error('order id must be non-blank')
    if (!Number.isSafeInteger(definition.reward) || definition.reward < 0) {
      throw new Error(`order '${definition.id}' reward must be a nonnegative safe integer`)
    }
    if (byId.has(definition.id)) throw new Error(`duplicate order id '${definition.id}'`)
    byId.set(definition.id, definition)
  }
  for (const definition of definitions) {
    const prerequisites = new Set<OrderId>()
    for (const prerequisite of definition.prerequisites) {
      if (prerequisite === definition.id) throw new Error(`order '${definition.id}' cannot depend on itself`)
      if (prerequisites.has(prerequisite)) throw new Error(`order '${definition.id}' has duplicate prerequisite '${prerequisite}'`)
      prerequisites.add(prerequisite)
      if (!byId.has(prerequisite)) throw new Error(`order '${definition.id}' requires missing order '${prerequisite}'`)
    }
  }

  const visited = new Set<OrderId>()
  const visiting = new Set<OrderId>()
  const visit = (id: OrderId): void => {
    if (visited.has(id)) return
    if (visiting.has(id)) throw new Error(`order prerequisites contain a cycle at '${id}'`)
    visiting.add(id)
    for (const prerequisite of byId.get(id)!.prerequisites) visit(prerequisite)
    visiting.delete(id)
    visited.add(id)
  }
  for (const definition of definitions) visit(definition.id)
}

export function decodeOrderCatalog(value: unknown): OrderCatalogRevision {
  if (!Array.isArray(value)) throw new Error('order catalog must be an array')
  const definitions = value.map(decodeDefinition)
  validateOrderCatalog(definitions)
  const byId = new Map<OrderId, OrderDefinition>()
  for (const definition of definitions) byId.set(definition.id, definition)
  const revision = Object.freeze({
    definitions: Object.freeze(definitions),
    byId,
  })
  decodedRevisions.add(revision)
  return revision
}

export class LiveOrderCatalog {
  readonly #listeners = new Set<(revision: OrderCatalogRevision) => void>()

  public constructor(private revision: OrderCatalogRevision) {
    if (!decodedRevisions.has(revision)) throw new Error('live order catalog requires a decoded revision')
  }

  public get current(): OrderCatalogRevision {
    return this.revision
  }

  public definition(id: string): OrderDefinition | undefined {
    return this.revision.byId.get(id)
  }

  public publish(revision: OrderCatalogRevision): void {
    if (!decodedRevisions.has(revision)) throw new Error('live order catalog requires a decoded revision')
    this.revision = revision
    for (const listener of this.#listeners) listener(revision)
  }

  public subscribe(listener: (revision: OrderCatalogRevision) => void): () => void {
    this.#listeners.add(listener)
    return () => { this.#listeners.delete(listener) }
  }
}

function decodeOpeningOrderCatalog(): OrderCatalogRevision {
  let content: unknown
  try {
    content = JSON.parse(openingOrderContent)
  } catch (error) {
    throw new Error(`opening order catalog JSON is malformed: ${error instanceof Error ? error.message : String(error)}`)
  }
  return decodeOrderCatalog(content)
}

export const openingOrderCatalog = new LiveOrderCatalog(decodeOpeningOrderCatalog())

export const STARTER_ORDER_ID = 'blank-sprout'

export const ORDER_CATALOG: readonly OrderDefinition[] = Object.freeze(
  openingOrderCatalog.current.definitions.map((definition) => Object.freeze({
    ...definition,
    title: definition.id,
    description: definition.formula ?? '',
  })),
)

export function availableOrderIds(
  progress: OrderProgress,
  orderAllowed: (orderId: string) => boolean,
): readonly OrderId[] {
  return openingOrderCatalog.current.definitions.flatMap((definition) => {
    const state = progress.orders.get(definition.id)
    if (state?.kind !== 'pending' || !orderAllowed(definition.id)) return []
    const unlocked = definition.prerequisites.every((id) => progress.orders.get(id)?.kind === 'completed')
    return unlocked ? [definition.id] : []
  })
}
