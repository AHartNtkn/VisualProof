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

export type SaveOperation = 'list' | 'create' | 'load' | 'update-tree' | 'update-camera'

export type SaveTransport = {
  request(operation: SaveOperation, input: Record<string, unknown>): Promise<unknown>
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

export function createSaveClient(transport: SaveTransport): SaveClient {
  return {
    list: () => transport.request('list', {}).then(decodeSlotList),
    create: (displayName, camera, trees) => transport.request('create', {
      displayName, camera, trees,
    }).then(decodeCreatedSlot),
    load: (slotId) => transport.request('load', { slotId }).then(decodeLoadedSlot),
    updateTree: (slotId, update) => transport.request('update-tree', { slotId, update })
      .then((value) => value as number),
    updateCamera: (slotId, camera) => transport.request('update-camera', { slotId, camera })
      .then(() => undefined),
  }
}

export const tauriSaveTransport: SaveTransport = {
  request(operation, input) {
    switch (operation) {
      case 'list': return invoke('list_slots')
      case 'create': return invoke('create_slot', { input })
      case 'load': return invoke('load_slot', input)
      case 'update-tree': return invoke('update_tree', input)
      case 'update-camera': return invoke('update_camera', input)
    }
  },
}

const playtestPaths: Record<SaveOperation, string> = {
  list: '/__orchard_playtest/save/list',
  create: '/__orchard_playtest/save/create',
  load: '/__orchard_playtest/save/load',
  'update-tree': '/__orchard_playtest/save/update-tree',
  'update-camera': '/__orchard_playtest/save/update-camera',
}

export function httpSaveTransport(config: {
  baseUrl: string
  token: string
  fetch: typeof globalThis.fetch
}): SaveTransport {
  const baseUrl = config.baseUrl.replace(/\/$/, '')
  return {
    async request(operation, input): Promise<unknown> {
      const response = await config.fetch(`${baseUrl}${playtestPaths[operation]}`, {
        method: 'POST',
        headers: {
          'content-type': 'application/json',
          'x-orchard-playtest-token': config.token,
        },
        body: JSON.stringify(input),
      })
      if (!response.ok) throw new Error(await response.text())
      return response.json()
    },
  }
}

function selectedSaveTransport(): SaveTransport {
  const transportName = import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri'
  switch (transportName) {
    case 'tauri': return tauriSaveTransport
    case 'playtest-http': {
      const baseUrl = import.meta.env.VITE_ORCHARD_PLAYTEST_URL
      const token = import.meta.env.VITE_ORCHARD_PLAYTEST_TOKEN
      if (baseUrl === undefined || token === undefined) {
        throw new Error('playtest HTTP save transport requires VITE_ORCHARD_PLAYTEST_URL and VITE_ORCHARD_PLAYTEST_TOKEN')
      }
      return httpSaveTransport({ baseUrl, token, fetch: globalThis.fetch })
    }
    default: throw new Error(`unsupported Orchard save transport '${transportName}'`)
  }
}

export const saveClient = createSaveClient(selectedSaveTransport())
