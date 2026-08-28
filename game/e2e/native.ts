import { $, browser, expect } from '@wdio/globals'
import { join } from 'node:path'
import { DatabaseSync } from 'node:sqlite'
import { Key } from 'webdriverio'

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

export async function settledDisplayedPose(): Promise<DisplayPose> {
  let previous = ''
  let stableSamples = 0
  let settled: DisplayPose | null = null
  await browser.waitUntil(async () => {
    const current = await displayedPose()
    const serialized = JSON.stringify(current)
    stableSamples = serialized === previous ? stableSamples + 1 : 0
    previous = serialized
    settled = current
    return stableSamples >= 2
  }, { interval: 20, timeout: 2_000, timeoutMsg: 'displayed camera pose did not settle after input ended' })
  if (settled === null) throw new Error('displayed camera pose did not produce a sample')
  return settled
}

export function expectPoseClose(actual: DisplayPose, expected: DisplayPose): void {
  for (const axis of ['x', 'y', 'z'] as const) {
    expect(actual.eye[axis]).toBeCloseTo(expected.eye[axis], 7)
    expect(actual.direction[axis]).toBeCloseTo(expected.direction[axis], 7)
  }
}

export async function hold(key: string, milliseconds = 180): Promise<void> {
  await browser.action('key').down(key).pause(milliseconds).up(key).perform()
}

export async function holdTogether(keys: readonly string[], milliseconds: number): Promise<void> {
  const action = browser.action('key')
  for (const key of keys) action.down(key)
  action.pause(milliseconds)
  for (const key of [...keys].reverse()) action.up(key)
  await action.perform()
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

export function expectDoubleCut(before: StoredDiagram, after: StoredDiagram, parent: string): void {
  const added = Object.keys(after.regions).filter((id) => before.regions[id] === undefined)
  expect(added).toHaveLength(2)
  const outer = added.find((id) => after.regions[id]?.kind === 'cut' && after.regions[id].parent === parent)
  expect(outer).toBeDefined()
  const inner = added.find((id) => after.regions[id]?.kind === 'cut' && after.regions[id].parent === outer)
  expect(inner).toBeDefined()
}

export async function waitForVisibleTreeTween(): Promise<void> {
  const worldCanvas = await canvas()
  const elementId = await worldCanvas.elementId
  const during = await browser.takeElementScreenshot(elementId)
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

export async function setRenderMode(mode: 'game' | 'raw'): Promise<void> {
  await browser.execute((nextMode) => window.__ORCHARD_WDIO__?.setRenderMode(nextMode), mode)
}

export async function pressEscape(): Promise<void> {
  await browser.keys(Key.Escape)
}
