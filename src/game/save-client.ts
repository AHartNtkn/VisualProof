import { invoke } from '@tauri-apps/api/core'
import { decodeLoadedSlot } from './model'
import type { GameWorld } from './model'
import type { GameTree } from './model'
import { ORDER_CATALOG, type OrderProgress, type PotPlacement } from './orders/catalog'

export type { PotPlacement } from './orders/catalog'

export type CameraRecord = {
  readonly x: number
  readonly y: number
  readonly z: number
  readonly yaw: number
  readonly pitch: number
}

export type TreeUpdate = {
  readonly treeId: string
  readonly diagramJson: string
  readonly x: number
  readonly z: number
  readonly yaw: number
}

type PendingOrderRecordWire = {
  readonly orderId: string
  readonly state: 'pending'
  readonly pot: null
}

type AcceptedOrderRecordWire = {
  readonly orderId: string
  readonly state: 'accepted'
  readonly pot: PotPlacement
}

type CompletedOrderRecordWire = {
  readonly orderId: string
  readonly state: 'completed'
  readonly pot: null
}

export type OrderRecordWire =
  | PendingOrderRecordWire
  | AcceptedOrderRecordWire
  | CompletedOrderRecordWire

export type CreateSlotState = {
  readonly displayName: string
  readonly camera: CameraRecord
  readonly trees: readonly TreeUpdate[]
  readonly reputation: number
  readonly orders: readonly OrderRecordWire[]
}

export function treeUpdateFromGameTree(tree: GameTree): TreeUpdate {
  return {
    treeId: tree.id,
    diagramJson: tree.snapshot.json,
    x: tree.placement.x,
    z: tree.placement.z,
    yaw: tree.placement.yaw,
  }
}

export type SlotListEntry = {
  readonly slotId: string
  readonly displayName: string
  readonly updatedAtMs: number
  readonly error: string | null
}

export type SaveClient = {
  readonly list: () => Promise<readonly SlotListEntry[]>
  readonly create: (state: CreateSlotState) => Promise<SlotListEntry>
  readonly load: (slotId: string) => Promise<GameWorld>
  readonly updateTree: (slotId: string, update: TreeUpdate) => Promise<number>
  readonly insertTree: (slotId: string, update: TreeUpdate) => Promise<number>
  readonly updateCamera: (slotId: string, camera: CameraRecord) => Promise<void>
  readonly acceptOrder: (slotId: string, orderId: string, pot: PotPlacement) => Promise<void>
  readonly abandonOrder: (slotId: string, orderId: string) => Promise<void>
  readonly completeOrder: (slotId: string, orderId: string, reward: number) => Promise<number>
}

export type SaveOperation =
  | 'list'
  | 'create'
  | 'load'
  | 'update-tree'
  | 'insert-tree'
  | 'update-camera'
  | 'accept-order'
  | 'abandon-order'
  | 'complete-order'

export type SaveTransport = {
  request(operation: SaveOperation, input: Record<string, unknown>): Promise<unknown>
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

function decodeSlotEntry(value: unknown, what: string): SlotListEntry {
  const entry = record(value, what)
  const allowed = new Set(['slotId', 'displayName', 'updatedAtMs', 'error'])
  for (const key of Object.keys(entry)) {
    if (!allowed.has(key)) throw new Error(`${what} has unknown field '${key}'`)
  }
  if (typeof entry.slotId !== 'string') throw new Error(`${what}.slotId must be a string`)
  if (typeof entry.displayName !== 'string') {
    throw new Error(`${what}.displayName must be a string`)
  }
  if (typeof entry.updatedAtMs !== 'number' || !Number.isSafeInteger(entry.updatedAtMs)) {
    throw new Error(`${what}.updatedAtMs must be a safe integer`)
  }
  if (entry.error !== null && typeof entry.error !== 'string') {
    throw new Error(`${what}.error must be a string or null`)
  }
  return {
    slotId: entry.slotId,
    displayName: entry.displayName,
    updatedAtMs: entry.updatedAtMs,
    error: entry.error,
  }
}

export function decodeSlotList(value: unknown): readonly SlotListEntry[] {
  if (!Array.isArray(value)) throw new Error('slot list must be an array')
  const ids = new Set<string>()
  return value.map((entry, index) => {
    const decoded = decodeSlotEntry(entry, `slot ${index}`)
    if (ids.has(decoded.slotId)) throw new Error(`duplicate slot id '${decoded.slotId}'`)
    ids.add(decoded.slotId)
    return decoded
  })
}

export function decodeCreatedSlot(value: unknown): SlotListEntry {
  return decodeSlotEntry(value, 'created slot')
}

function assertCatalogOrderIds(orderIds: Iterable<string>, what: string): void {
  const expected = ORDER_CATALOG.map(({ id }) => id)
  const actual = new Set<string>()
  for (const id of orderIds) {
    if (actual.has(id)) throw new Error(`${what} must match the authored order catalog`)
    actual.add(id)
  }
  if (actual.size !== expected.length || expected.some((id) => !actual.has(id))) {
    throw new Error(`${what} must match the authored order catalog`)
  }
}

function nonnegativeSafeInteger(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) {
    throw new Error(`${what} must be a nonnegative safe integer`)
  }
  return value
}

function finiteNumber(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    throw new Error(`${what} must be a finite number`)
  }
  return value
}

function validateCreateOrder(value: unknown): string {
  const order = exactRecord(value, ['orderId', 'state', 'pot'], 'create state order')
  if (typeof order.orderId !== 'string') throw new Error('create state order.orderId must be a string')
  const { orderId } = order
  if (typeof order.state !== 'string') {
    throw new Error(`create state order '${orderId}'.state must be a string`)
  }
  switch (order.state) {
    case 'pending':
      if (order.pot !== null) throw new Error(`create state order '${orderId}' pending state requires a null pot`)
      return orderId
    case 'completed':
      if (order.pot !== null) throw new Error(`create state order '${orderId}' completed state requires a null pot`)
      return orderId
    case 'accepted': {
      if (order.pot === null) throw new Error(`create state order '${orderId}' accepted state requires a pot`)
      const pot = exactRecord(order.pot, ['x', 'z', 'yaw'], `create state order '${orderId}'.pot`)
      finiteNumber(pot.x, `create state order '${orderId}'.pot.x`)
      finiteNumber(pot.z, `create state order '${orderId}'.pot.z`)
      finiteNumber(pot.yaw, `create state order '${orderId}'.pot.yaw`)
      return orderId
    }
    default: throw new Error(`create state order '${orderId}' has unknown state '${order.state}'`)
  }
}

function validateCreateState(state: CreateSlotState): void {
  nonnegativeSafeInteger(state.reputation, 'create state.reputation')
  assertCatalogOrderIds(state.orders.map(validateCreateOrder), 'create state orders')
}

export function orderRecordsFromProgress(progress: OrderProgress): readonly OrderRecordWire[] {
  assertCatalogOrderIds(progress.orders.keys(), 'progress orders')
  return ORDER_CATALOG.map(({ id }) => {
    const order = progress.orders.get(id)!
    switch (order.kind) {
      case 'pending': return { orderId: id, state: 'pending', pot: null }
      case 'accepted': return { orderId: id, state: 'accepted', pot: order.pot }
      case 'completed': return { orderId: id, state: 'completed', pot: null }
    }
  })
}

function decodeNumber(value: unknown, what: string): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value)) {
    throw new Error(`${what} must be a safe integer`)
  }
  return value
}

function decodeVoid(value: unknown, what: string): void {
  if (value !== null) throw new Error(`${what} must be null`)
}

export function createSaveClient(transport: SaveTransport): SaveClient {
  return {
    list: () => transport.request('list', {}).then(decodeSlotList),
    create: async (state) => {
      validateCreateState(state)
      return decodeCreatedSlot(await transport.request('create', state))
    },
    load: (slotId) => transport.request('load', { slotId }).then(decodeLoadedSlot),
    updateTree: (slotId, update) => transport.request('update-tree', { slotId, update })
      .then((value) => decodeNumber(value, 'updated tree revision')),
    insertTree: (slotId, update) => transport.request('insert-tree', { slotId, update })
      .then((value) => decodeNumber(value, 'inserted tree revision')),
    updateCamera: (slotId, camera) => transport.request('update-camera', { slotId, camera })
      .then((value) => decodeVoid(value, 'updated camera response')),
    acceptOrder: (slotId, orderId, pot) => transport.request('accept-order', { slotId, orderId, pot })
      .then((value) => decodeVoid(value, 'accepted order response')),
    abandonOrder: (slotId, orderId) => transport.request('abandon-order', { slotId, orderId })
      .then((value) => decodeVoid(value, 'abandoned order response')),
    completeOrder: (slotId, orderId, reward) => transport.request('complete-order', { slotId, orderId, reward })
      .then((value) => nonnegativeSafeInteger(value, 'completed order reputation')),
  }
}

export const tauriSaveTransport: SaveTransport = {
  request(operation, input) {
    switch (operation) {
      case 'list': return invoke('list_slots')
      case 'create': return invoke('create_slot', { input })
      case 'load': return invoke('load_slot', input)
      case 'update-tree': return invoke('update_tree', input)
      case 'insert-tree': return invoke('insert_tree', input)
      case 'update-camera': return invoke('update_camera', input)
      case 'accept-order': return invoke('accept_order', input)
      case 'abandon-order': return invoke('abandon_order', input)
      case 'complete-order': return invoke('complete_order', input)
    }
  },
}

const playtestPaths: Record<SaveOperation, string> = {
  list: '/__orchard_playtest/save/list',
  create: '/__orchard_playtest/save/create',
  load: '/__orchard_playtest/save/load',
  'update-tree': '/__orchard_playtest/save/update-tree',
  'insert-tree': '/__orchard_playtest/save/insert-tree',
  'update-camera': '/__orchard_playtest/save/update-camera',
  'accept-order': '/__orchard_playtest/save/accept-order',
  'abandon-order': '/__orchard_playtest/save/abandon-order',
  'complete-order': '/__orchard_playtest/save/complete-order',
}

export function httpSaveTransport(config: {
  baseUrl: string
  token: string
  fetch: typeof globalThis.fetch
}): SaveTransport {
  const baseUrl = config.baseUrl.replace(/\/$/, '')
  return {
    async request(operation, input): Promise<unknown> {
      let response: Response
      try {
        response = await config.fetch.call(globalThis, `${baseUrl}${playtestPaths[operation]}`, {
          method: 'POST',
          headers: {
            'content-type': 'application/json',
            'x-orchard-playtest-token': config.token,
          },
          body: JSON.stringify(input),
        })
      } catch (error) {
        const detail = error instanceof Error ? error.message : String(error)
        throw new Error(`browser playtest save service unavailable: ${detail}`)
      }
      if (!response.ok) throw new Error(await response.text())
      return response.json()
    },
  }
}

export function selectSaveTransport(config: {
  transportName: string
  baseUrl?: string
  token?: string
  fetch: typeof globalThis.fetch
}): SaveTransport {
  switch (config.transportName) {
    case 'tauri': return tauriSaveTransport
    case 'playtest-http': {
      const { baseUrl, token } = config
      if (baseUrl === undefined || baseUrl.trim().length === 0
        || token === undefined || token.trim().length === 0) {
        throw new Error('playtest HTTP save transport requires VITE_ORCHARD_PLAYTEST_URL and VITE_ORCHARD_PLAYTEST_TOKEN')
      }
      return httpSaveTransport({ baseUrl, token, fetch: config.fetch })
    }
    default: throw new Error(`unsupported Orchard save transport '${config.transportName}'`)
  }
}

export const saveClient = createSaveClient(selectSaveTransport({
  transportName: import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri',
  baseUrl: import.meta.env.VITE_ORCHARD_PLAYTEST_URL,
  token: import.meta.env.VITE_ORCHARD_PLAYTEST_TOKEN,
  fetch: globalThis.fetch,
}))
