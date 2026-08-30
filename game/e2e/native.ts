import { $, browser, expect } from '@wdio/globals'
import { execFileSync } from 'node:child_process'
import { join } from 'node:path'
import { DatabaseSync } from 'node:sqlite'
import { Key } from 'webdriverio'
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

export async function waitForMenu(): Promise<void> {
  const start = $('[data-start]')
  try {
    await browser.waitUntil(async () => {
      if (!await start.isDisplayed()) return false
      return !await $('[data-slot-loading]').isDisplayed()
    }, { timeout: 5_000, interval: 100 })
  } catch (error) {
    const body = $('body')
    const html = $('html')
    throw new Error(
      `menu did not become ready: start.hidden=${String(await start.getAttribute('hidden'))}, `
      + `start.size=${JSON.stringify(await start.getSize())}, camera=${await game().getAttribute('data-camera-mode')}, `
      + `root.size=${JSON.stringify(await game().getSize())}, body.size=${JSON.stringify(await body.getSize())}, `
      + `html.size=${JSON.stringify(await html.getSize())}, root.display=${JSON.stringify(await game().getCSSProperty('display'))}, `
      + `root.width=${JSON.stringify(await game().getCSSProperty('width'))}, root.height=${JSON.stringify(await game().getCSSProperty('height'))}, `
      + `window=${JSON.stringify(await browser.getWindowSize())}, display=${JSON.stringify(await start.getCSSProperty('display'))}, `
      + `ready=${await game().getAttribute('data-ready')}, errors=${await game().getAttribute('data-errors')}, `
      + `url=${await browser.getUrl()}, title=${await browser.getTitle()}`,
      { cause: error },
    )
  }
}

export async function createSlot(name: string, tutorialsEnabled = true): Promise<string> {
  await waitForMenu()
  await $('[data-new-slot-name]').setValue(name)
  const tutorials = $('[data-create-tutorials]')
  if (await tutorials.isSelected() !== tutorialsEnabled) await tutorials.click()
  await $('[data-create-slot]').click()
  await browser.waitUntil(async () => {
    if (await attribute('ready') === 'true') return true
    const error = await attribute('errors')
    if (error.length > 0) throw new Error(`creating the native save failed: ${error}`)
    return false
  }, { timeout: 30_000, interval: 100 })
  return attribute('loaded-slot')
}

export async function soleSlotId(): Promise<string> {
  await waitForMenu()
  const load = $('[data-load-slot]')
  await load.waitForDisplayed()
  const slotId = await load.getAttribute('data-load-slot')
  if (slotId === null || slotId.length === 0) throw new Error('expected one saved orchard')
  return slotId
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

export async function moveFreeCameraTo(
  target: { readonly x: number; readonly y: number; readonly z: number },
): Promise<void> {
  for (let attempt = 0; attempt < 14; attempt++) {
    const pose = await displayedPose()
    const horizontalLength = Math.hypot(pose.direction.x, pose.direction.z)
    if (horizontalLength === 0) throw new Error('cannot move through a vertical view')
    const forward = {
      x: pose.direction.x / horizontalLength,
      z: pose.direction.z / horizontalLength,
    }
    const right = { x: -forward.z, z: forward.x }
    const delta = {
      x: target.x - pose.eye.x,
      y: target.y - pose.eye.y,
      z: target.z - pose.eye.z,
    }
    const forwardDistance = delta.x * forward.x + delta.z * forward.z
    const rightDistance = delta.x * right.x + delta.z * right.z
    if (Math.abs(forwardDistance) >= 0.06) {
      await hold(
        forwardDistance > 0 ? 'w' : 's',
        Math.max(12, Math.min(500, Math.round(Math.abs(forwardDistance) * 125))),
      )
    }
    if (Math.abs(rightDistance) >= 0.06) {
      await hold(
        rightDistance > 0 ? 'd' : 'a',
        Math.max(12, Math.min(500, Math.round(Math.abs(rightDistance) * 125))),
      )
    }
    if (Math.abs(delta.y) >= 0.06) {
      await hold(
        delta.y > 0 ? Key.Space : Key.Control,
        Math.max(12, Math.min(500, Math.round(Math.abs(delta.y) * 125))),
      )
    }
    const current = await displayedPose()
    if (Math.hypot(
      current.eye.x - target.x,
      current.eye.y - target.y,
      current.eye.z - target.z,
    ) < 0.12) return
  }
  const current = await displayedPose()
  expect(Math.hypot(
    current.eye.x - target.x,
    current.eye.y - target.y,
    current.eye.z - target.z,
  )).toBeLessThan(0.16)
}

export async function aimReticleAt(
  point: { readonly x: number; readonly y: number; readonly z: number },
  horizontalDistance = 7,
): Promise<void> {
  const { direction } = await displayedPose()
  const horizontalLength = Math.hypot(direction.x, direction.z)
  if (horizontalLength === 0) throw new Error('cannot aim the reticle through a vertical view')
  const distance = horizontalDistance / horizontalLength
  await moveFreeCameraTo({
    x: point.x - direction.x * distance,
    y: point.y - direction.y * distance,
    z: point.z - direction.z * distance,
  })
  await lookReticleAt(point)
}

export async function lookReticleAt(
  point: { readonly x: number; readonly y: number; readonly z: number },
): Promise<void> {
  for (let attempt = 0; attempt < 4; attempt++) {
    const pose = await displayedPose()
    const delta = {
      x: point.x - pose.eye.x,
      y: point.y - pose.eye.y,
      z: point.z - pose.eye.z,
    }
    const length = Math.hypot(delta.x, delta.y, delta.z)
    if (length === 0) throw new Error('cannot aim the reticle from the target point')
    const desired = { x: delta.x / length, y: delta.y / length, z: delta.z / length }
    const alignment = Math.max(-1, Math.min(1,
      pose.direction.x * desired.x + pose.direction.y * desired.y + pose.direction.z * desired.z,
    ))
    if (Math.acos(alignment) < 0.003) return
    const currentYaw = Math.atan2(-pose.direction.x, -pose.direction.z)
    const desiredYaw = Math.atan2(-desired.x, -desired.z)
    const currentPitch = Math.asin(pose.direction.y)
    const desiredPitch = Math.asin(desired.y)
    const yawDelta = Math.atan2(
      Math.sin(currentYaw - desiredYaw),
      Math.cos(currentYaw - desiredYaw),
    )
    await moveDesktopPointer(
      Math.round(yawDelta / 0.002),
      Math.round((currentPitch - desiredPitch) / 0.002),
    )
  }
  const pose = await displayedPose()
  const delta = { x: point.x - pose.eye.x, y: point.y - pose.eye.y, z: point.z - pose.eye.z }
  const length = Math.hypot(delta.x, delta.y, delta.z)
  expect((
    pose.direction.x * delta.x + pose.direction.y * delta.y + pose.direction.z * delta.z
  ) / length).toBeGreaterThan(Math.cos(0.006))
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
  return elementScreenshot(canvas())
}

export async function canvasCenterScreenshot(size = 320): Promise<string> {
  const screenshot = Buffer.from(await canvasScreenshot(), 'base64')
  return execFileSync(
    'convert',
    ['png:-', '-gravity', 'center', '-crop', `${size}x${size}+0+0`, '+repage', '-strip', 'png:-'],
    { env: process.env, input: screenshot, stdio: ['pipe', 'pipe', 'pipe'] },
  ).toString('base64')
}

export async function elementScreenshot(element: ReturnType<typeof $>): Promise<string> {
  await element.waitForDisplayed()
  const screenshot = Buffer.from(await browser.takeScreenshot(), 'base64')
  const pngWidth = screenshot.readUInt32BE(16)
  const pngHeight = screenshot.readUInt32BE(20)
  const viewport = await browser.execute(() => ({
    width: window.innerWidth,
    height: window.innerHeight,
  }))
  const location = await element.getLocation()
  const size = await element.getSize()
  const scaleX = pngWidth / viewport.width
  const scaleY = pngHeight / viewport.height
  const x = Math.round(location.x * scaleX)
  const y = Math.round(location.y * scaleY)
  const width = Math.max(1, Math.round(size.width * scaleX))
  const height = Math.max(1, Math.round(size.height * scaleY))
  return execFileSync(
    'convert',
    ['png:-', '-crop', `${width}x${height}+${x}+${y}`, '+repage', '-strip', 'png:-'],
    { env: process.env, input: screenshot, stdio: ['pipe', 'pipe', 'pipe'] },
  ).toString('base64')
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
  const database = new DatabaseSync(
    join(dataRoot, 'com.visualproofassistant.orchard', 'saves', `${validatedSlotId}.sqlite3`),
    { readOnly: true },
  )
  database.exec('PRAGMA busy_timeout = 5000')
  return database
}

export type StoredTree = {
  readonly id: string
  readonly x: number
  readonly z: number
  readonly yaw: number
  readonly diagram: StoredDiagram
}

export function storedTree(slotId: string, treeId: string): StoredTree {
  const database = storedDatabase(slotId)
  try {
    const row = database.prepare(`
      SELECT trees.tree_id, trees.x, trees.z, trees.yaw, diagrams.diagram_json
      FROM trees
      JOIN diagrams ON diagrams.diagram_key = trees.diagram_key
      WHERE trees.tree_id = ?
    `).get(treeId) as {
      readonly tree_id?: unknown
      readonly x?: unknown
      readonly z?: unknown
      readonly yaw?: unknown
      readonly diagram_json?: unknown
    } | undefined
    if (
      row?.tree_id !== treeId
      || typeof row.x !== 'number'
      || typeof row.z !== 'number'
      || typeof row.yaw !== 'number'
      || typeof row.diagram_json !== 'string'
    ) throw new Error(`tree '${treeId}' is missing from save '${slotId}'`)
    return {
      id: treeId,
      x: row.x,
      z: row.z,
      yaw: row.yaw,
      diagram: JSON.parse(row.diagram_json) as StoredDiagram,
    }
  } finally {
    database.close()
  }
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

export function storedOrderIds(slotId: string): readonly string[] {
  const database = storedDatabase(slotId)
  try {
    const rows = database.prepare('SELECT order_id FROM orders ORDER BY order_id').all() as readonly {
      readonly order_id?: unknown
    }[]
    return rows.map(({ order_id: orderId }) => {
      if (typeof orderId !== 'string') throw new Error(`save '${slotId}' contains an invalid order ID`)
      return orderId
    })
  } finally {
    database.close()
  }
}

export function storedTutorialProgress(slotId: string): {
  readonly enabled: boolean
  readonly completed: readonly string[]
  readonly acquiredTools: readonly string[]
} {
  const database = storedDatabase(slotId)
  try {
    const progress = database.prepare(`
      SELECT tutorials_enabled FROM progress WHERE singleton = 1
    `).get() as { readonly tutorials_enabled?: unknown } | undefined
    if (progress?.tutorials_enabled !== 0 && progress?.tutorials_enabled !== 1) {
      throw new Error(`tutorial preference is missing from save '${slotId}'`)
    }
    const identifiers = (table: 'tutorial_milestones' | 'acquired_tools', column: string): readonly string[] => (
      database.prepare(`SELECT ${column} AS id FROM ${table} ORDER BY ${column}`).all() as readonly {
        readonly id?: unknown
      }[]
    ).map(({ id }) => {
      if (typeof id !== 'string') throw new Error(`invalid identifier in ${table}`)
      return id
    })
    return {
      enabled: progress.tutorials_enabled === 1,
      completed: identifiers('tutorial_milestones', 'milestone_id'),
      acquiredTools: identifiers('acquired_tools', 'tool_id'),
    }
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

export async function moveDesktopPointer(x: number, y: number): Promise<void> {
  execFileSync('xdotool', ['mousemove_relative', '--', String(x), String(y)], {
    env: process.env,
    stdio: 'pipe',
  })
  await browser.pause(60)
}

export async function pressDesktopKey(key: string): Promise<void> {
  execFileSync('xdotool', ['key', '--clearmodifiers', key], {
    env: process.env,
    stdio: 'pipe',
  })
  await browser.pause(60)
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
