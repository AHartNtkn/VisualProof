import { $, browser, expect } from '@wdio/globals'
import { join } from 'node:path'
import { DatabaseSync } from 'node:sqlite'
import { validateNativeSlotId } from './slot-id'

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

export function expectDoubleCut(
  before: StoredDiagram,
  after: StoredDiagram,
  parent: string,
): void {
  const added = Object.keys(after.regions).filter((id) => before.regions[id] === undefined)
  expect(added).toHaveLength(2)
  const outer = added.find((id) =>
    after.regions[id]?.kind === 'cut' && after.regions[id].parent === parent,
  )
  expect(outer).toBeDefined()
  const inner = added.find((id) => after.regions[id]?.kind === 'cut' && after.regions[id].parent === outer)
  expect(inner).toBeDefined()
}

export async function canvasScreenshot(): Promise<string> {
  const worldCanvas = await canvas()
  const elementId = await worldCanvas.elementId
  return browser.takeElementScreenshot(elementId)
}

export async function waitForVisibleTreeTween(before?: string): Promise<void> {
  const worldCanvas = await canvas()
  const elementId = await worldCanvas.elementId
  const during = before ?? await browser.takeElementScreenshot(elementId)
  let previous = ''
  let settled = ''
  let stableSamples = 0
  await browser.waitUntil(async () => {
    const current = await browser.takeElementScreenshot(elementId)
    stableSamples = current === previous ? stableSamples + 1 : 0
    previous = current
    settled = current
    return stableSamples >= 2
  }, { interval: 75, timeout: 2_000, timeoutMsg: 'tree tween did not visibly settle' })
  expect(settled).not.toEqual(during)
  await expect(game()).toHaveAttribute('data-save-state', 'idle')
}

export async function clickWorld(x = 0, y = 0): Promise<void> {
  await browser.action('pointer')
    .move({ origin: await canvas(), x, y })
    .down({ button: 0 })
    .up({ button: 0 })
    .perform()
}

function storedDatabase(slotId: string): DatabaseSync {
  const validatedSlotId = validateNativeSlotId(slotId)
  const dataRoot = process.env['GAME_E2E_DATA_ROOT']
  if (dataRoot === undefined) throw new Error('GAME_E2E_DATA_ROOT is required for save inspection')
  return new DatabaseSync(
    join(dataRoot, 'com.visualproofassistant.orchard', 'saves', `${validatedSlotId}.sqlite3`),
    { readOnly: true },
  )
}

export function storedTreeIds(slotId: string): readonly string[] {
  const database = storedDatabase(slotId)
  try {
    const rows = database.prepare('SELECT tree_id FROM trees ORDER BY tree_id').all() as readonly {
      readonly tree_id?: unknown
    }[]
    return rows.map(({ tree_id: treeId }) => {
      if (typeof treeId !== 'string') throw new Error(`save '${slotId}' contains an invalid tree ID`)
      return treeId
    })
  } finally {
    database.close()
  }
}

export function storedOrder(
  slotId: string,
  orderId: string,
): {
  readonly state: 'pending' | 'accepted' | 'completed'
  readonly pot: { readonly x: number; readonly z: number; readonly yaw: number } | null
} {
  const database = storedDatabase(slotId)
  try {
    const row = database.prepare(`
      SELECT state, pot_x, pot_z, pot_yaw
      FROM orders
      WHERE order_id = ?
    `).get(orderId) as {
      readonly state?: unknown
      readonly pot_x?: unknown
      readonly pot_z?: unknown
      readonly pot_yaw?: unknown
    } | undefined
    if (row === undefined || !['pending', 'accepted', 'completed'].includes(String(row.state))) {
      throw new Error(`order '${orderId}' is missing from save '${slotId}'`)
    }
    const state = row.state as 'pending' | 'accepted' | 'completed'
    if (state !== 'accepted') {
      if (row.pot_x !== null || row.pot_z !== null || row.pot_yaw !== null) {
        throw new Error(`order '${orderId}' has a pot outside accepted state`)
      }
      return { state, pot: null }
    }
    if (
      typeof row.pot_x !== 'number'
      || typeof row.pot_z !== 'number'
      || typeof row.pot_yaw !== 'number'
    ) throw new Error(`order '${orderId}' has an invalid accepted pot`)
    return { state, pot: { x: row.pot_x, z: row.pot_z, yaw: row.pot_yaw } }
  } finally {
    database.close()
  }
}

export function storedReputation(slotId: string): number {
  const database = storedDatabase(slotId)
  try {
    const row = database.prepare(`
      SELECT reputation
      FROM progress
      WHERE singleton = 1
    `).get() as { readonly reputation?: unknown } | undefined
    if (typeof row?.reputation !== 'number' || !Number.isSafeInteger(row.reputation)) {
      throw new Error(`reputation is missing from save '${slotId}'`)
    }
    return row.reputation
  } finally {
    database.close()
  }
}

export function storedTreeDiagram(slotId: string, treeId: string): StoredDiagram {
  const database = storedDatabase(slotId)
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
  const database = storedDatabase(slotId)
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
  await browser.action('pointer').move({ origin: 'pointer', x, y }).perform()
}

export async function dragWorld(
  button: 0 | 1 | 2,
  from: { readonly x: number; readonly y: number },
  to: { readonly x: number; readonly y: number },
): Promise<void> {
  await browser.action('pointer')
    .move({ origin: await canvas(), x: from.x, y: from.y })
    .down({ button })
    .move({ origin: await canvas(), x: to.x, y: to.y, duration: 120 })
    .up({ button })
    .perform()
}

export async function wheelWorld(deltaY: number): Promise<void> {
  await browser.action('wheel')
    .scroll({ origin: await canvas(), deltaX: 0, deltaY })
    .perform()
}

export async function canvasOffsetForWorldPoint(
  pose: DisplayPose,
  point: { readonly x: number; readonly y: number; readonly z: number },
): Promise<{ readonly x: number; readonly y: number }> {
  const forward = pose.direction
  const rightLength = Math.hypot(forward.z, forward.x)
  if (rightLength === 0) throw new Error('cannot project through a vertical camera')
  const right = { x: -forward.z / rightLength, y: 0, z: forward.x / rightLength }
  const up = {
    x: right.y * forward.z - right.z * forward.y,
    y: right.z * forward.x - right.x * forward.z,
    z: right.x * forward.y - right.y * forward.x,
  }
  const delta = {
    x: point.x - pose.eye.x,
    y: point.y - pose.eye.y,
    z: point.z - pose.eye.z,
  }
  const depth = delta.x * forward.x + delta.y * forward.y + delta.z * forward.z
  if (depth <= 0) throw new Error('world point is behind the camera')
  const horizontal = delta.x * right.x + delta.y * right.y + delta.z * right.z
  const vertical = delta.x * up.x + delta.y * up.y + delta.z * up.z
  const height = (await canvas().getSize()).height
  const pixelsPerWorld = height / (2 * depth * Math.tan((67 * Math.PI) / 360))
  return {
    x: Math.round(horizontal * pixelsPerWorld),
    y: Math.round(-vertical * pixelsPerWorld),
  }
}

export async function setRenderMode(mode: 'game' | 'raw'): Promise<void> {
  await browser.execute((nextMode) => window.__ORCHARD_WDIO__?.setRenderMode(nextMode), mode)
}
