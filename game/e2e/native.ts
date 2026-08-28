import { $, browser, expect } from '@wdio/globals'
import { join } from 'node:path'
import { DatabaseSync } from 'node:sqlite'

export type DisplayPose = {
  readonly eye: { readonly x: number; readonly y: number; readonly z: number }
  readonly direction: { readonly x: number; readonly y: number; readonly z: number }
}

export type StoredDiagram = {
  readonly root: string
  readonly regions: Readonly<Record<string, { readonly kind: 'sheet' } | { readonly kind: 'cut'; readonly parent: string }>>
  readonly nodes: Readonly<Record<string, unknown>>
  readonly wires: Readonly<Record<string, unknown>>
}

export const game = () => $('[data-game]')
export const canvas = () => $('[data-world] canvas')

export async function attribute(name: string): Promise<string> {
  const value = await game().getAttribute(`data-${name}`)
  if (value === null) throw new Error(`missing data-${name}`)
  return value
}

export async function numberAttribute(name: string): Promise<number> {
  const value = Number(await attribute(name))
  if (!Number.isFinite(value)) throw new Error(`data-${name} is not finite`)
  return value
}

export async function displayedPose(): Promise<DisplayPose> {
  return {
    eye: JSON.parse(await attribute('displayed-eye')) as DisplayPose['eye'],
    direction: JSON.parse(await attribute('displayed-direction')) as DisplayPose['direction'],
  }
}

export function expectPoseClose(actual: DisplayPose, expected: DisplayPose): void {
  for (const axis of ['x', 'y', 'z'] as const) {
    expect(actual.eye[axis]).toBeCloseTo(expected.eye[axis], 7)
    expect(actual.direction[axis]).toBeCloseTo(expected.direction[axis], 7)
  }
}

export function expectEyeClose(actual: DisplayPose, expected: DisplayPose): void {
  for (const axis of ['x', 'y', 'z'] as const) {
    expect(actual.eye[axis]).toBeCloseTo(expected.eye[axis], 7)
  }
}

export function expectDirectionClose(actual: DisplayPose, expected: DisplayPose): void {
  for (const axis of ['x', 'y', 'z'] as const) {
    expect(actual.direction[axis]).toBeCloseTo(expected.direction[axis], 7)
  }
}

export function poseEyeDistance(actual: DisplayPose, expected: DisplayPose): number {
  return Math.hypot(
    actual.eye.x - expected.eye.x,
    actual.eye.y - expected.eye.y,
    actual.eye.z - expected.eye.z,
  )
}

export function poseDirectionDistance(actual: DisplayPose, expected: DisplayPose): number {
  return Math.hypot(
    actual.direction.x - expected.direction.x,
    actual.direction.y - expected.direction.y,
    actual.direction.z - expected.direction.z,
  )
}

export async function hold(key: string, milliseconds = 180): Promise<void> {
  await browser.action('key').down(key).pause(milliseconds).up(key).perform()
}

export async function createSlot(name: string): Promise<string> {
  await $('[data-new-slot-name]').setValue(name)
  await $('[data-create-slot]').click()
  await browser.waitUntil(async () => {
    if (await attribute('ready') === 'true') return true
    const error = await attribute('errors')
    if (error.length > 0) throw new Error(`creating the native save failed: ${error}`)
    return false
  }, { timeout: 30_000, interval: 100 })
  return attribute('loaded-slot')
}

export async function loadSlot(slotId: string): Promise<void> {
  const load = $(`[data-load-slot="${slotId}"]`)
  await load.waitForDisplayed()
  await load.click()
  await expect(game()).toHaveAttribute('data-loaded-slot', slotId)
  await expect(game()).toHaveAttribute('data-ready', 'true')
}

export async function rightClickWorld(x = 0, y = 0): Promise<void> {
  await browser.action('pointer')
    .move({ origin: await canvas(), x, y })
    .down({ button: 2 })
    .up({ button: 2 })
    .perform()
}

export async function clickWorld(x = 0, y = 0): Promise<void> {
  await browser.action('pointer')
    .move({ origin: await canvas(), x, y })
    .down({ button: 0 })
    .up({ button: 0 })
    .perform()
}

export function storedTreeDiagram(slotId: string, treeId: string): StoredDiagram {
  const dataRoot = process.env['GAME_E2E_DATA_ROOT']
  if (dataRoot === undefined) throw new Error('GAME_E2E_DATA_ROOT is required for save inspection')
  const database = new DatabaseSync(
    join(dataRoot, 'com.visualproofassistant.orchard', 'saves', `${slotId}.sqlite3`),
    { readOnly: true },
  )
  try {
    const row = database.prepare(`
      SELECT diagrams.diagram_json AS diagram_json
      FROM trees
      JOIN diagrams ON diagrams.diagram_key = trees.diagram_key
      WHERE trees.tree_id = ?
    `).get(treeId) as { readonly diagram_json?: unknown } | undefined
    if (typeof row?.diagram_json !== 'string') throw new Error(`tree '${treeId}' is missing from save '${slotId}'`)
    return JSON.parse(row.diagram_json) as StoredDiagram
  } finally {
    database.close()
  }
}

export function storedCameraPose(slotId: string): DisplayPose {
  const dataRoot = process.env['GAME_E2E_DATA_ROOT']
  if (dataRoot === undefined) throw new Error('GAME_E2E_DATA_ROOT is required for save inspection')
  const database = new DatabaseSync(
    join(dataRoot, 'com.visualproofassistant.orchard', 'saves', `${slotId}.sqlite3`),
    { readOnly: true },
  )
  try {
    const row = database.prepare(`
      SELECT x, y, z, yaw, pitch
      FROM camera
      WHERE singleton = 1
    `).get() as {
      readonly x?: unknown
      readonly y?: unknown
      readonly z?: unknown
      readonly yaw?: unknown
      readonly pitch?: unknown
    } | undefined
    if (
      typeof row?.x !== 'number'
      || typeof row.y !== 'number'
      || typeof row.z !== 'number'
      || typeof row.yaw !== 'number'
      || typeof row.pitch !== 'number'
    ) throw new Error(`camera is missing from save '${slotId}'`)
    const horizontal = Math.cos(row.pitch)
    return {
      eye: { x: row.x, y: row.y, z: row.z },
      direction: {
        x: -Math.sin(row.yaw) * horizontal,
        y: Math.sin(row.pitch),
        z: -Math.cos(row.yaw) * horizontal,
      },
    }
  } finally {
    database.close()
  }
}

export async function movePointer(x: number, y: number): Promise<void> {
  await browser.action('pointer').move({ origin: await canvas(), x, y }).perform()
}

export async function setRenderMode(mode: 'game' | 'raw'): Promise<void> {
  await browser.execute((nextMode) => window.__ORCHARD_WDIO__?.setRenderMode(nextMode), mode)
}
