import type { DiagramSnapshot } from './diagram-snapshot'
import { snapshotFromJson } from './diagram-snapshot'
import {
  MAX_REPUTATION,
  openingOrderCatalog,
  type OrderCatalogRevision,
  type OrderProgress,
  type OrderState,
} from './orders/catalog'

export type GameProgress = OrderProgress & {
  readonly tutorialsEnabled: boolean
  readonly completedTutorialMilestones: ReadonlySet<string>
  readonly acquiredToolIds: ReadonlySet<string>
}

export type CameraPose = {
  readonly position: { readonly x: number; readonly y: number; readonly z: number }
  readonly yaw: number
  readonly pitch: number
}

export type TreeTarget = {
  readonly treeId: string
  readonly center: { readonly x: number; readonly y: number; readonly z: number }
  readonly radius: number
}

export type GameTree = {
  readonly id: string
  readonly snapshot: DiagramSnapshot
  readonly placement: { readonly x: number; readonly z: number; readonly yaw: number }
}

export type GameWorld = {
  readonly slot: { readonly id: string; readonly name: string; readonly updatedAtMs: number }
  readonly camera: CameraPose
  readonly trees: ReadonlyMap<string, GameTree>
  readonly progress: GameProgress
}

function record(value: unknown, what: string): Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error(`${what} must be an object`)
  }
  return value as Record<string, unknown>
}

function exactRecord(value: unknown, keys: readonly string[], what: string): Record<string, unknown> {
  const result = record(value, what)
  const allowed = new Set(keys)
  for (const key of Object.keys(result)) {
    if (!allowed.has(key)) throw new Error(`${what} has unknown field '${key}'`)
  }
  return result
}

function string(value: unknown, what: string): string {
  if (typeof value !== 'string') throw new Error(`${what} must be a string`)
  return value
}

function finiteNumber(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    throw new Error(`${what} must be a finite number`)
  }
  return value
}

function safeInteger(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value)) {
    throw new Error(`${what} must be a safe integer`)
  }
  return value
}

function array(value: unknown, what: string): readonly unknown[] {
  if (!Array.isArray(value)) throw new Error(`${what} must be an array`)
  return value
}

function nonnegativeSafeInteger(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isInteger(value) || value < 0 || value > MAX_REPUTATION) {
    throw new Error(`${what} must be a nonnegative safe integer`)
  }
  return value
}

function decodeOrderProgress(
  reputationValue: unknown,
  ordersValue: unknown,
  catalog: OrderCatalogRevision,
): OrderProgress {
  const reputation = nonnegativeSafeInteger(reputationValue, 'loaded slot.reputation')
  const orders = new Map<string, OrderState>()
  for (const value of array(ordersValue, 'loaded slot.orders')) {
    const wire = exactRecord(value, ['orderId', 'state', 'pot'], 'order')
    const orderId = string(wire.orderId, 'order.orderId')
    if (orders.has(orderId)) throw new Error(`duplicate order id '${orderId}'`)
    const state = string(wire.state, `order '${orderId}'.state`)
    switch (state) {
      case 'pending':
        if (wire.pot !== null) throw new Error(`order '${orderId}' pending state requires a null pot`)
        orders.set(orderId, { kind: 'pending' })
        break
      case 'completed':
        if (wire.pot !== null) throw new Error(`order '${orderId}' completed state requires a null pot`)
        orders.set(orderId, { kind: 'completed' })
        break
      case 'accepted': {
        const pot = exactRecord(wire.pot, ['x', 'z', 'yaw'], `order '${orderId}'.pot`)
        orders.set(orderId, {
          kind: 'accepted',
          pot: {
            x: finiteNumber(pot.x, `order '${orderId}'.pot.x`),
            z: finiteNumber(pot.z, `order '${orderId}'.pot.z`),
            yaw: finiteNumber(pot.yaw, `order '${orderId}'.pot.yaw`),
          },
        })
        break
      }
      default: throw new Error(`order '${orderId}' has unknown state '${state}'`)
    }
  }
  const catalogIds = catalog.definitions.map(({ id }) => id)
  if (orders.size !== catalogIds.length || catalogIds.some((id) => !orders.has(id))) {
    throw new Error('loaded slot.orders must match the authored order catalog')
  }
  return { reputation, orders }
}

function decodeDiagramJson(diagramJson: string, what: string): DiagramSnapshot {
  try {
    return snapshotFromJson(diagramJson)
  } catch (error) {
    throw new Error(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
}

function decodeIdentifierSet(value: unknown, singular: string, plural: string): ReadonlySet<string> {
  const result = new Set<string>()
  for (const item of array(value, `loaded slot.${plural}`)) {
    const id = string(item, `loaded slot.${singular}`)
    if (id.trim().length === 0) throw new Error(`${singular} must be a non-blank string`)
    if (result.has(id)) throw new Error(`duplicate ${singular} '${id}'`)
    result.add(id)
  }
  return result
}

export function decodeLoadedSlot(
  value: unknown,
  catalog: OrderCatalogRevision = openingOrderCatalog.current,
): GameWorld {
  const loaded = exactRecord(
    value,
    [
      'slotId',
      'displayName',
      'updatedAtMs',
      'camera',
      'trees',
      'diagrams',
      'reputation',
      'orders',
      'tutorialsEnabled',
      'completedTutorialMilestones',
      'acquiredToolIds',
    ],
    'loaded slot',
  )
  const slotId = string(loaded.slotId, 'loaded slot.slotId')
  const displayName = string(loaded.displayName, 'loaded slot.displayName')
  const updatedAtMs = safeInteger(loaded.updatedAtMs, 'loaded slot.updatedAtMs')
  const orderProgress = decodeOrderProgress(loaded.reputation, loaded.orders, catalog)
  if (typeof loaded.tutorialsEnabled !== 'boolean') {
    throw new Error('loaded slot.tutorialsEnabled must be a boolean')
  }
  const progress: GameProgress = {
    ...orderProgress,
    tutorialsEnabled: loaded.tutorialsEnabled,
    completedTutorialMilestones: decodeIdentifierSet(
      loaded.completedTutorialMilestones,
      'completed tutorial milestone id',
      'completedTutorialMilestones',
    ),
    acquiredToolIds: decodeIdentifierSet(loaded.acquiredToolIds, 'acquired tool id', 'acquiredToolIds'),
  }

  const camera = exactRecord(
    loaded.camera,
    ['x', 'y', 'z', 'yaw', 'pitch'],
    'camera',
  )
  const cameraPose: CameraPose = {
    position: {
      x: finiteNumber(camera.x, 'camera.x'),
      y: finiteNumber(camera.y, 'camera.y'),
      z: finiteNumber(camera.z, 'camera.z'),
    },
    yaw: finiteNumber(camera.yaw, 'camera.yaw'),
    pitch: finiteNumber(camera.pitch, 'camera.pitch'),
  }

  const diagramsByKey = new Map<number, DiagramSnapshot>()
  const diagramsByJson = new Map<string, DiagramSnapshot>()
  for (const [index, value] of array(loaded.diagrams, 'loaded slot.diagrams').entries()) {
    const wire = exactRecord(value, ['diagramKey', 'diagramJson'], `diagram ${index}`)
    const key = safeInteger(wire.diagramKey, `diagram ${index}.diagramKey`)
    if (diagramsByKey.has(key)) throw new Error(`duplicate diagram key ${key}`)
    const json = string(wire.diagramJson, `diagram ${index}.diagramJson`)
    let snapshot = diagramsByJson.get(json)
    if (snapshot === undefined) {
      snapshot = decodeDiagramJson(json, `diagram ${index}`)
      diagramsByJson.set(json, snapshot)
    }
    diagramsByKey.set(key, snapshot)
  }

  const trees = new Map<string, GameTree>()
  for (const [index, value] of array(loaded.trees, 'loaded slot.trees').entries()) {
    const wire = exactRecord(
      value,
      ['treeId', 'diagramKey', 'x', 'z', 'yaw'],
      `tree ${index}`,
    )
    const id = string(wire.treeId, `tree ${index}.treeId`)
    if (trees.has(id)) throw new Error(`duplicate tree id '${id}'`)
    const diagramKey = safeInteger(wire.diagramKey, `tree '${id}'.diagramKey`)
    const storedDiagram = diagramsByKey.get(diagramKey)
    if (storedDiagram === undefined) {
      throw new Error(`tree '${id}' references missing diagram key ${diagramKey}`)
    }
    trees.set(id, {
      id,
      snapshot: storedDiagram,
      placement: {
        x: finiteNumber(wire.x, `tree '${id}'.x`),
        z: finiteNumber(wire.z, `tree '${id}'.z`),
        yaw: finiteNumber(wire.yaw, `tree '${id}'.yaw`),
      },
    })
  }

  return {
    slot: { id: slotId, name: displayName, updatedAtMs },
    camera: cameraPose,
    trees,
    progress,
  }
}
