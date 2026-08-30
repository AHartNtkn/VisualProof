import { $, $$, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import { TOOL_CATALOG, type ToolId } from '../../src/game/tools'
import {
  aimReticleAt,
  attribute,
  createSlot,
  displayedPose,
  game,
  loadSlot,
  moveFreeCameraTo,
  rightClickWorld,
  soleSlotId,
  storedOrder,
  storedOrderIds,
  storedReputation,
  storedTreeDiagram,
  storedTreeIds,
} from './native'

const ORDER_IDS = [
  'blank-sprout',
  'single-double-cut',
  'irregular-double-cut-a',
  'irregular-double-cut-b',
] as const
const SOURCE_ID = 'tree-0000'

async function waitForSave(): Promise<void> {
  await expect(game()).toHaveAttribute('data-save-state', 'idle')
}

async function openLedger(tab: 'tools' | 'orders'): Promise<void> {
  await browser.keys('Tab')
  await expect($('[data-ledger]')).toBeDisplayed()
  if (await attribute('ledger-tab') !== tab) await $(`[data-ledger-primary="${tab}"]`).click()
  await expect(game()).toHaveAttribute('data-ledger-tab', tab)
}

async function acquire(toolId: 'double-cut' | 'iteration'): Promise<void> {
  const action = $(`[data-tool-id="${toolId}"] [data-tool-action="acquire"]`)
  await action.waitForDisplayed()
  await action.click()
  await expect(game()).toHaveAttribute('data-selected-tool', toolId)
}

async function assertVisibleToolCycle(selectedTool: ToolId): Promise<string> {
  const presentation = await browser.execute(() => {
    const rowElements = [...document.querySelectorAll<HTMLElement>('.tool-selector-row')]
    const visibleHighlights = rowElements.filter((row) => {
      const style = getComputedStyle(row)
      return style.borderLeftStyle !== 'none'
        && Number.parseFloat(style.borderLeftWidth) > 0
        && style.borderLeftColor !== 'transparent'
        && style.borderLeftColor !== 'rgba(0, 0, 0, 0)'
    })
    const held = document.querySelector<HTMLElement>('[data-held-tool-model]')!
    const silhouette = held.querySelector<HTMLElement>('[data-held-tool-silhouette]')!
    return {
      labels: rowElements.map(({ innerText }) => innerText),
      rowsVisible: rowElements.map((row) => {
        const style = getComputedStyle(row)
        const bounds = row.getBoundingClientRect()
        return style.display !== 'none'
          && style.visibility === 'visible'
          && Number.parseFloat(style.opacity) > 0
          && bounds.width > 0
          && bounds.height > 0
      }),
      highlighted: visibleHighlights.map((row) => ({
        id: row.dataset['toolId'],
        background: getComputedStyle(row).backgroundColor,
        border: getComputedStyle(row).borderLeftColor,
      })),
      heldId: silhouette.dataset['toolId'],
      heldSilhouette: silhouette.dataset['silhouette'],
      heldVisible: held.getBoundingClientRect().width > 0 && held.getBoundingClientRect().height > 0,
    }
  })
  const expected = TOOL_CATALOG.find(({ id }) => id === selectedTool)!
  expect(presentation.labels).toEqual(TOOL_CATALOG.map(({ label }) => label))
  expect(presentation.rowsVisible).toEqual(TOOL_CATALOG.map(() => true))
  expect(presentation.highlighted).toHaveLength(1)
  expect(presentation.highlighted[0]).toMatchObject({ id: expected.id })
  expect(presentation.highlighted[0]!.background).not.toBe('rgba(0, 0, 0, 0)')
  expect(presentation.highlighted[0]!.border).not.toBe('rgba(0, 0, 0, 0)')
  expect(presentation.heldId).toBe(expected.id)
  expect(presentation.heldSilhouette).toBe(expected.silhouette)
  expect(presentation.heldVisible).toBe(true)

  const held = await $('[data-held-tool-model]')
  return await browser.takeElementScreenshot(await held.elementId)
}

async function selectTool(toolId: 'sprout-spawner' | 'double-cut' | 'iteration'): Promise<void> {
  for (let attempt = 0; attempt < 4; attempt++) {
    if (await attribute('selected-tool') === toolId) return
    await browser.keys('1')
  }
  await expect(game()).toHaveAttribute('data-selected-tool', toolId)
}

async function accept(orderId: string): Promise<void> {
  await openLedger('orders')
  const action = $(`[data-order-id="${orderId}"] [data-order-action="accept"]`)
  await action.waitForDisplayed()
  await action.click()
  await expect($('[data-feedback]')).toHaveText(`Accepted ${orderId}.`)
  await expect(game()).toHaveAttribute('data-ledger-open', 'false')
  await waitForSave()
}

async function takeWholeTree(tree: { readonly x: number; readonly z: number }): Promise<void> {
  await aimReticleAt({ ...tree, y: 0.25 })
  await rightClickWorld()
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Whole-tree cutting held from'))
  await expect(game()).toHaveAttribute('data-cutting-held', 'true')
}

async function deliver(slotId: string, orderId: string): Promise<void> {
  const pot = storedOrder(slotId, orderId).pot
  if (pot === null) throw new Error(`order '${orderId}' has no accepted pot`)
  await aimReticleAt({ x: pot.x + 0.85, y: 0.55, z: pot.z })
  await rightClickWorld()
  await expect($('[data-feedback]')).toHaveText(expect.stringContaining(`Completed ${orderId}.`))
  await expect(game()).toHaveAttribute('data-cutting-held', 'false')
  await waitForSave()
}

describe('orchard order lifecycle', () => {
  const phase = process.env['GAME_E2E_PHASE']

  it('uses the four authored IDs, acquired-tool cycle, independent pots, and native lifecycle controls', async () => {
    if (phase === 'play') {
      const slotId = await createSlot('Order Lifecycle', false)
      expect(storedOrderIds(slotId)).toEqual([...ORDER_IDS].sort())
      await expect(game()).toHaveAttribute('data-selected-tool', 'sprout-spawner')

      await openLedger('tools')
      await acquire('double-cut')
      await acquire('iteration')
      await browser.keys('Tab')
      await expect(game()).toHaveAttribute('data-ledger-open', 'false')

      const heldPresentations: string[] = []
      for (const tool of TOOL_CATALOG) {
        await browser.keys('1')
        heldPresentations.push(await assertVisibleToolCycle(tool.id))
      }
      expect(new Set(heldPresentations).size).toBe(TOOL_CATALOG.length)
      await browser.waitUntil(async () => !(await $('.tool-selector-row').isExisting()), {
        timeout: 3_000,
        timeoutMsg: 'three-tool selector did not fade',
      })
      await expect($('.tool-selector-category')).not.toExist()

      await moveFreeCameraTo({ x: 0, y: 1.7, z: 12 })
      await accept('blank-sprout')
      expect(storedOrder(slotId, 'blank-sprout').state).toBe('accepted')
      expect(storedOrder(slotId, 'single-double-cut').state).toBe('pending')
      return
    }

    const slotId = await soleSlotId()
    await loadSlot(slotId)

    if (phase === 'reload') {
      await selectTool('iteration')
      await takeWholeTree({ x: 0, z: 0 })
      const heldPose = await displayedPose()
      await browser.keys('Escape')
      await expect($('[data-pause]')).toBeDisplayed()
      await expect(game()).toHaveAttribute('data-cutting-held', 'true')
      await expect(game()).toHaveAttribute('data-selected-tool', 'iteration')
      await $('[data-pause-resume]').click()
      await expect(game()).toHaveAttribute('data-cutting-held', 'true')
      await expect(displayedPose()).resolves.toEqual(heldPose)

      await browser.keys('Backspace')
      await expect($('[data-feedback]')).toHaveText('Cutting cleared.')
      await expect(game()).toHaveAttribute('data-cutting-held', 'false')
      await expect(game()).toHaveAttribute('data-camera-mode', 'free')

      await takeWholeTree({ x: 0, z: 0 })
      await deliver(slotId, 'blank-sprout')
      expect(storedOrder(slotId, 'blank-sprout')).toEqual({ state: 'completed', pot: null })
      expect(storedReputation(slotId)).toBe(1)

      await moveFreeCameraTo({ x: 8, y: 1.7, z: 12 })
      await accept('single-double-cut')
      await selectTool('double-cut')
      const before = storedTreeDiagram(slotId, SOURCE_ID)
      await aimReticleAt({ x: 0, y: 0.25, z: 0 })
      await rightClickWorld()
      await expect($('[data-feedback]')).toHaveText(`Double cut applied to ${SOURCE_ID}.`)
      await browser.waitUntil(() => Object.keys(storedTreeDiagram(slotId, SOURCE_ID).regions).length
        === Object.keys(before.regions).length + 2)

      await selectTool('iteration')
      await takeWholeTree({ x: 0, z: 0 })
      await deliver(slotId, 'single-double-cut')
      expect(storedOrder(slotId, 'single-double-cut')).toEqual({ state: 'completed', pot: null })
      expect(storedReputation(slotId)).toBe(2)
      return
    }

    if (phase !== 'verify') throw new Error(`unknown order-loop phase '${String(phase)}'`)
    expect(storedTreeIds(slotId)).toEqual([SOURCE_ID])
    expect(storedOrder(slotId, 'blank-sprout').state).toBe('completed')
    expect(storedOrder(slotId, 'single-double-cut').state).toBe('completed')
    expect(storedReputation(slotId)).toBe(2)

    await openLedger('orders')
    const availableIds: Array<string | null> = []
    for (const element of await $$('[data-order-id]')) {
      availableIds.push(await element.getAttribute('data-order-id'))
    }
    expect(new Set(availableIds)).toEqual(new Set([
      'irregular-double-cut-a',
      'irregular-double-cut-b',
    ]))
    await $(`[data-order-id="irregular-double-cut-b"] [data-order-action="accept"]`).click()
    await expect(game()).toHaveAttribute('data-ledger-open', 'false')
    await moveFreeCameraTo({ x: -8, y: 1.7, z: 12 })
    await accept('irregular-double-cut-a')

    const first = storedOrder(slotId, 'irregular-double-cut-a')
    const second = storedOrder(slotId, 'irregular-double-cut-b')
    expect(first.state).toBe('accepted')
    expect(second.state).toBe('accepted')
    expect(first.pot).not.toEqual(second.pot)

    await openLedger('orders')
    await $('[data-ledger-context="active"]').click()
    await expect($$('[data-order-action="abandon"]')).toBeElementsArrayOfSize(2)
    await $(`[data-order-id="irregular-double-cut-a"] [data-order-action="abandon"]`).click()
    await waitForSave()
    expect(storedOrder(slotId, 'irregular-double-cut-a')).toEqual({ state: 'pending', pot: null })
    expect(storedOrder(slotId, 'irregular-double-cut-b').state).toBe('accepted')
    expect(await attribute('errors')).toBe('')
  })
})
