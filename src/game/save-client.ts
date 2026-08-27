import { invoke } from '@tauri-apps/api/core'
import { decodeLoadedSlot } from './model'
import type { GameWorld } from './model'

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

export type SlotListEntry = {
  readonly slotId: string
  readonly displayName: string
  readonly updatedAtMs: number
  readonly error: string | null
}

export type SaveClient = {
  readonly list: () => Promise<readonly SlotListEntry[]>
  readonly create: (
    displayName: string,
    camera: CameraRecord,
    trees: readonly TreeUpdate[],
  ) => Promise<SlotListEntry>
  readonly load: (slotId: string) => Promise<GameWorld>
  readonly updateTree: (slotId: string, update: TreeUpdate) => Promise<number>
  readonly updateCamera: (slotId: string, camera: CameraRecord) => Promise<void>
}

function record(value: unknown, what: string): Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error(`${what} must be an object`)
  }
  return value as Record<string, unknown>
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

export const saveClient: SaveClient = {
  list: () => invoke('list_slots').then(decodeSlotList),
  create: (displayName, camera, trees) => invoke('create_slot', {
    input: { displayName, camera, trees },
  }).then(decodeCreatedSlot),
  load: (slotId) => invoke('load_slot', { slotId }).then(decodeLoadedSlot),
  updateTree: (slotId, update) => invoke('update_tree', { slotId, update }),
  updateCamera: (slotId, camera) => invoke('update_camera', { slotId, camera }),
}
