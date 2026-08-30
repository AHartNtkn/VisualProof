import { readFileSync, writeFileSync } from 'node:fs'
import { $, browser, expect } from '@wdio/globals'
import { after, describe, it } from 'mocha'
import {
  aimReticleAt,
  attribute,
  canvasCenterScreenshot,
  createSlot,
  elementScreenshot,
  game,
  loadSlot,
  moveFreeCameraTo,
  pressDesktopKey,
  rightClickWorld,
  storedOrder,
  storedOrderIds,
  storedTree,
  storedTreeDiagram,
  storedTreeIds,
  waitForMenu,
} from './native'

const contentPath = new URL('../content/orders.json', import.meta.url)
const startingContent = readFileSync(contentPath)
const CREATED_ID = 'developer-blank'
const REMEMBERED_FORMULA = '∀P:o. ¬¬P'

after(() => {
  writeFileSync(contentPath, startingContent)
})

async function waitForSave(): Promise<void> {
  await expect(game()).toHaveAttribute('data-save-state', 'idle')
}

async function openLedger(tab: 'tools' | 'orders'): Promise<void> {
  if (await attribute('ledger-open') !== 'true') await browser.keys('Tab')
  await expect($('[data-ledger]')).toBeDisplayed()
  if (await attribute('ledger-tab') !== tab) await $(`[data-ledger-primary="${tab}"]`).click()
  await expect(game()).toHaveAttribute('data-ledger-tab', tab)
}

async function selectTool(toolId: 'sprout-spawner' | 'double-cut' | 'iteration'): Promise<void> {
  for (let attempt = 0; attempt < 4; attempt++) {
    if (await attribute('selected-tool') === toolId) return
    await browser.keys('1')
  }
  await expect(game()).toHaveAttribute('data-selected-tool', toolId)
}

async function setDeveloperTools(enabled: boolean): Promise<void> {
  if (await attribute('ledger-open') === 'true') await browser.keys('Tab')
  await browser.keys('Escape')
  await $('[data-pause-settings]').click()
  const checkbox = $('[data-settings-developer-tools]')
  if (await checkbox.isSelected() !== enabled) await checkbox.click()
  await expect(checkbox).toBeSelected({ wait: 1000, reverse: !enabled })
  await $('[data-settings-back]').click()
  await $('[data-pause-resume]').click()
}

async function toggleDeveloperMode(enabled: boolean): Promise<void> {
  if ((await attribute('developer-mode') === 'true') !== enabled) await pressDesktopKey('grave')
  await expect(game()).toHaveAttribute('data-developer-mode', String(enabled))
}

async function takeWholeTree(point: { readonly x: number; readonly z: number }): Promise<void> {
  await selectTool('iteration')
  await aimReticleAt({ ...point, y: 0.25 })
  await rightClickWorld()
  await expect(game()).toHaveAttribute('data-cutting-held', 'true')
}

async function expectDeliveryMismatch(
  slotId: string,
  orderId: string,
  source: { readonly x: number; readonly z: number },
): Promise<void> {
  await takeWholeTree(source)
  const before = storedOrder(slotId, orderId)
  const pot = before.pot
  if (pot === null) throw new Error(`order '${orderId}' has no active pot`)
  await aimReticleAt({ x: pot.x + 0.85, y: 0.55, z: pot.z })
  await rightClickWorld()
  await expect($('[data-feedback]')).toHaveText(`delivered proposition does not match order '${orderId}'`)
  await expect(game()).toHaveAttribute('data-cutting-held', 'true')
  expect(storedOrder(slotId, orderId)).toEqual(before)
  await browser.keys('Backspace')
  await expect(game()).toHaveAttribute('data-cutting-held', 'false')
}

async function settledScreenshot(capture: () => Promise<string>): Promise<string> {
  let previous = ''
  let stableSamples = 0
  await browser.waitUntil(async () => {
    const current = await capture()
    stableSamples = current === previous ? stableSamples + 1 : 0
    previous = current
    return stableSamples >= 2
  }, { interval: 75, timeout: 2_000, timeoutMsg: 'developer evidence did not visually settle' })
  return previous
}

describe('developer order content', () => {
  it('publishes formula edits atomically and creates, reloads, and deletes checked-in orders', async () => {
    const slotId = await createSlot('Developer Orders', false)

    await aimReticleAt({ x: 8, y: -0.035, z: 0 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(expect.stringContaining('Planted sprout tree-'))
    await browser.waitUntil(() => storedTreeIds(slotId).length === 2)
    const sproutId = storedTreeIds(slotId).find((treeId) => treeId !== 'tree-0000')
    if (sproutId === undefined) throw new Error('the developer scenario did not persist its sprout')
    const sprout = storedTree(slotId, sproutId)

    await openLedger('tools')
    for (const toolId of ['double-cut', 'iteration'] as const) {
      const acquire = $(`[data-tool-id="${toolId}"] [data-tool-action="acquire"]`)
      await acquire.waitForDisplayed()
      await acquire.click()
    }
    await browser.keys('Tab')

    await moveFreeCameraTo({ x: -10, y: 1.7, z: 12 })
    await openLedger('orders')
    await $(`[data-order-id="blank-sprout"] [data-order-action="accept"]`).click()
    await waitForSave()
    expect(storedOrder(slotId, 'blank-sprout').state).toBe('accepted')

    await selectTool('double-cut')
    await aimReticleAt({ x: 0, y: 0.25, z: 0 })
    await rightClickWorld()
    await browser.waitUntil(() => Object.keys(storedTreeDiagram(slotId, 'tree-0000').regions).length === 3)
    await expectDeliveryMismatch(slotId, 'blank-sprout', { x: 0, z: 0 })

    await setDeveloperTools(true)
    await toggleDeveloperMode(true)
    await openLedger('orders')
    await $('[data-ledger-context="active"]').click()
    const tileSelector = '[data-order-id="blank-sprout"]'
    const tileBefore = await settledScreenshot(() => elementScreenshot($(tileSelector)))
    const potBefore = await settledScreenshot(canvasCenterScreenshot)
    await $(tileSelector).click()
    await expect(game()).toHaveAttribute('data-editor-state', 'edit')
    await expect($('[data-order-editor]')).toBeDisplayed()
    await expect($('[data-order-editor-formula]')).toHaveValue('')

    await $('[data-order-editor-formula]').setValue(REMEMBERED_FORMULA)
    await browser.keys('Escape')
    await expect($('[data-pause]')).toBeDisplayed()
    await expect($('[data-pause-resume]')).toBeFocused()
    const resume = $('[data-pause-resume]')
    const foreground = await browser.execute(() => {
      const control = document.querySelector<HTMLElement>('[data-pause-resume]')!
      const bounds = control.getBoundingClientRect()
      const hit = document.elementFromPoint(
        bounds.left + bounds.width / 2,
        bounds.top + bounds.height / 2,
      )
      return {
        tag: hit?.tagName ?? null,
        surface: hit?.closest('[data-pause], [data-order-editor]')?.hasAttribute('data-pause')
          ? 'pause'
          : 'order-editor',
      }
    })
    expect(foreground).toEqual({ tag: 'BUTTON', surface: 'pause' })
    await resume.click()
    await expect($('[data-pause]')).not.toBeDisplayed()
    await expect($('[data-order-editor]')).toBeDisplayed()
    await expect($('[data-order-editor-formula]')).toHaveValue(REMEMBERED_FORMULA)

    await $('[data-order-editor-cancel]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    expect(await settledScreenshot(() => elementScreenshot($(tileSelector)))).toBe(tileBefore)
    expect(await settledScreenshot(canvasCenterScreenshot)).toBe(potBefore)

    await $(tileSelector).click()
    await expect($('[data-order-editor-formula]')).toHaveValue('')
    await $('[data-order-editor-formula]').setValue(REMEMBERED_FORMULA)
    await $('[data-order-editor-save]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    await waitForSave()
    expect(readFileSync(contentPath, 'utf8')).toContain(REMEMBERED_FORMULA)
    expect(await settledScreenshot(() => elementScreenshot($(tileSelector)))).not.toBe(tileBefore)
    expect(await settledScreenshot(canvasCenterScreenshot)).not.toBe(potBefore)

    await $(tileSelector).click()
    await expect($('[data-order-editor-formula]')).toHaveValue(REMEMBERED_FORMULA)
    await $('[data-order-editor-cancel]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()

    if (await attribute('ledger-open') === 'true') await browser.keys('Tab')
    await expectDeliveryMismatch(slotId, 'blank-sprout', { x: sprout.x, z: sprout.z })

    await openLedger('orders')
    await $('[data-ledger-primary="orders"]').click()
    await expect(game()).toHaveAttribute('data-editor-state', 'create')
    await expect($('[data-order-editor-id]')).toHaveValue('')
    await expect($('[data-order-editor-reward]')).toHaveValue('1')
    await expect($('[data-order-editor-formula]')).toHaveValue('')
    await $('[data-order-editor-id]').setValue(CREATED_ID)
    await $('[data-order-editor-save]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    await waitForSave()
    expect(storedOrderIds(slotId)).toContain(CREATED_ID)
    expect(readFileSync(contentPath, 'utf8')).toContain(`"id": "${CREATED_ID}"`)

    await toggleDeveloperMode(false)
    await $('[data-ledger-context="available"]').click()
    await $(`[data-order-id="${CREATED_ID}"] [data-order-action="accept"]`).click()
    await waitForSave()
    expect(storedOrder(slotId, CREATED_ID).state).toBe('accepted')
    const acceptedPotFrame = await canvasCenterScreenshot()

    await browser.keys('Escape')
    await $('[data-pause-main-menu]').click()
    await waitForMenu()
    await loadSlot(slotId)
    expect(storedOrderIds(slotId)).toContain(CREATED_ID)
    expect(storedOrder(slotId, CREATED_ID).state).toBe('accepted')
    expect(readFileSync(contentPath, 'utf8')).toContain(`"id": "${CREATED_ID}"`)

    await toggleDeveloperMode(true)
    await openLedger('orders')
    await $('[data-ledger-context="active"]').click()
    await $(`[data-order-id="${CREATED_ID}"]`).click()
    await expect(game()).toHaveAttribute('data-editor-state', 'edit')
    await $('[data-order-editor-delete]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    await waitForSave()
    expect(storedOrderIds(slotId)).not.toContain(CREATED_ID)
    expect(readFileSync(contentPath, 'utf8')).not.toContain(`"id": "${CREATED_ID}"`)
    expect(await canvasCenterScreenshot()).not.toBe(acceptedPotFrame)
    await expect($(`[data-order-id="${CREATED_ID}"]`)).not.toExist()
    expect(await attribute('errors')).toBe('')
  })
})
