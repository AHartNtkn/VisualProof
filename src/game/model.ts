import type { DiagramSnapshot } from './diagram-snapshot'
import { snapshotFromJson } from './diagram-snapshot'

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

function decodeDiagramJson(diagramJson: string, what: string): DiagramSnapshot {
  try {
    return snapshotFromJson(diagramJson)
  } catch (error) {
    throw new Error(`${what}: ${error instanceof Error ? error.message : String(error)}`)
  }
}

export function decodeLoadedSlot(value: unknown): GameWorld {
  const loaded = exactRecord(
    value,
    ['slotId', 'displayName', 'updatedAtMs', 'camera', 'trees', 'diagrams'],
    'loaded slot',
  )
  const slotId = string(loaded.slotId, 'loaded slot.slotId')
  const displayName = string(loaded.displayName, 'loaded slot.displayName')
  const updatedAtMs = safeInteger(loaded.updatedAtMs, 'loaded slot.updatedAtMs')

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
  }
}
