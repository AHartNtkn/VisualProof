import { readFileSync, writeFileSync } from 'node:fs'
import { $, browser, expect } from '@wdio/globals'
import { after, describe, it } from 'mocha'
import { formulaToDiagram } from '../../src/formula'
import { DiagramBuilder, diagramFromJson, sameDiagram, type Diagram } from '../../src/kernel/diagram'
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
const tutorialContentPath = new URL('../content/tutorial.json', import.meta.url)
const toolContentPath = new URL('../content/tools.json', import.meta.url)
const startingContent = readFileSync(contentPath)
const startingTutorialContent = readFileSync(tutorialContentPath)
const startingToolContent = readFileSync(toolContentPath)
const CREATED_ID = 'developer-blank'
const REMEMBERED_FORMULA = '∀P:o. ¬¬P'
const EDITED_TUTORIAL = 'Move with W, A, S, and D.'
const EDITED_TOOL_NAME = 'Sprout Planter'
const EDITED_TOOL_DESCRIPTION = 'Right-click open ground to plant a new sprout.'

type PersistedOrderDefinition = {
  readonly id: string
  readonly prerequisites: readonly string[]
  readonly reward: number
  readonly goal: Diagram
  readonly formula?: string
}

function persistedCatalog(): readonly PersistedOrderDefinition[] {
  const content: unknown = JSON.parse(readFileSync(contentPath, 'utf8'))
  if (!Array.isArray(content)) throw new Error('persisted order catalog is not an array')
  return content.map((value, index) => {
    if (typeof value !== 'object' || value === null || Array.isArray(value)) {
      throw new Error(`persisted order ${index} is not an object`)
    }
    const record = value as Record<string, unknown>
    if (typeof record['id'] !== 'string') throw new Error(`persisted order ${index} has no string id`)
    if (!Array.isArray(record['prerequisites']) || record['prerequisites'].some((entry) => typeof entry !== 'string')) {
      throw new Error(`persisted order ${index} has malformed prerequisites`)
    }
    if (typeof record['reward'] !== 'number' || !Number.isSafeInteger(record['reward'])) {
      throw new Error(`persisted order ${index} has malformed reward`)
    }
    if (record['formula'] !== undefined && typeof record['formula'] !== 'string') {
      throw new Error(`persisted order ${index} has malformed formula`)
    }
    const common = {
      id: record['id'],
      prerequisites: record['prerequisites'] as string[],
      reward: record['reward'],
      goal: diagramFromJson(record['goal']),
    }
    return record['formula'] === undefined
      ? common
      : { ...common, formula: record['formula'] }
  })
}

function persistedOrderDefinition(orderId: string): PersistedOrderDefinition {
  const matches = persistedCatalog().filter(({ id }) => id === orderId)
  if (matches.length !== 1) {
    throw new Error(`expected exactly one persisted definition for '${orderId}', found ${matches.length}`)
  }
  return matches[0]!
}

function expectPersistedFormulaOrder(orderId: string, formula: string): void {
  const definition = persistedOrderDefinition(orderId)
  expect(definition.formula).toBe(formula)
  expect(sameDiagram(definition.goal, formulaToDiagram(formula))).toBe(true)
}

function expectPersistedBlankOrder(orderId: string): void {
  const definition = persistedOrderDefinition(orderId)
  expect(definition.prerequisites).toEqual([])
  expect(definition.reward).toBe(1)
  expect(definition.formula).toBeUndefined()
  expect(sameDiagram(definition.goal, new DiagramBuilder().build())).toBe(true)
}

function persistedTutorialText(milestoneId: string): string {
  const content = JSON.parse(readFileSync(tutorialContentPath, 'utf8')) as Array<{
    readonly milestoneId: string
    readonly text: string
  }>
  const definition = content.find((candidate) => candidate.milestoneId === milestoneId)
  if (definition === undefined) throw new Error(`persisted tutorial milestone '${milestoneId}' is missing`)
  return definition.text
}

function persistedTool(toolId: string): { readonly name: string; readonly description: string } {
  const content = JSON.parse(readFileSync(toolContentPath, 'utf8')) as Array<{
    readonly id: string
    readonly name: string
    readonly description: string
  }>
  const definition = content.find((candidate) => candidate.id === toolId)
  if (definition === undefined) throw new Error(`persisted tool '${toolId}' is missing`)
  return { name: definition.name, description: definition.description }
}

after(() => {
  writeFileSync(contentPath, startingContent)
  writeFileSync(tutorialContentPath, startingTutorialContent)
  writeFileSync(toolContentPath, startingToolContent)
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

async function setTutorials(enabled: boolean): Promise<void> {
  if (await attribute('ledger-open') === 'true') await browser.keys('Tab')
  await browser.keys('Escape')
  await $('[data-pause-settings]').click()
  const checkbox = $('[data-settings-tutorials]')
  if (await checkbox.isSelected() !== enabled) await checkbox.click()
  await expect(game()).toHaveAttribute('data-tutorials-enabled', String(enabled))
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

describe('developer content', () => {
  it('edits tutorial, tool, and order content through the running native application', async () => {
    const slotId = await createSlot('Developer Orders', false)

    await setDeveloperTools(true)
    await setTutorials(true)
    await toggleDeveloperMode(true)

    await $('[data-tutorial-card]').click()
    await expect($('[data-tutorial-editor]')).toBeDisplayed()
    await expect($('[data-tutorial-editor-id]')).toHaveValue('move')
    await $('[data-tutorial-editor-text]').setValue('Draft movement text')
    await browser.keys('Escape')
    await expect($('[data-pause]')).toBeDisplayed()
    await expect($('[data-tutorial-editor]')).toBeDisplayed()
    await $('[data-pause-resume]').click()
    await expect($('[data-tutorial-editor-text]')).toHaveValue('Draft movement text')
    await $('[data-tutorial-editor-id]').click()
    await browser.keys('Backspace')
    await expect($('[data-tutorial-editor]')).not.toBeDisplayed()

    await $('[data-tutorial-card]').click()
    await $('[data-tutorial-editor-text]').setValue(EDITED_TUTORIAL)
    await $('[data-tutorial-editor-save]').click()
    await expect($('[data-tutorial-editor]')).not.toBeDisplayed()
    await expect($('[data-tutorial-instruction]')).toHaveText(EDITED_TUTORIAL)
    expect(persistedTutorialText('move')).toBe(EDITED_TUTORIAL)

    await openLedger('tools')
    const acquiredTab = $('[data-ledger-context="acquired"]')
    await acquiredTab.click()
    await expect(acquiredTab).toHaveAttribute('aria-pressed', 'true')
    const sproutTile = $('[data-ledger] [data-tool-id="sprout-spawner"]')
    await expect(sproutTile).toBeDisplayed()
    await sproutTile.click()
    await expect($('[data-tool-editor]')).toBeDisplayed()
    await expect($('[data-tool-editor-id]')).toHaveValue('sprout-spawner')
    await $('[data-tool-editor-name]').setValue(EDITED_TOOL_NAME)
    await $('[data-tool-editor-description]').setValue(EDITED_TOOL_DESCRIPTION)
    await $('[data-tool-editor-save]').click()
    await expect($('[data-tool-editor]')).not.toBeDisplayed()
    await expect(sproutTile).toHaveText(expect.stringContaining(EDITED_TOOL_NAME))
    await expect(sproutTile).toHaveText(expect.stringContaining(EDITED_TOOL_DESCRIPTION))
    expect(persistedTool('sprout-spawner')).toEqual({
      name: EDITED_TOOL_NAME,
      description: EDITED_TOOL_DESCRIPTION,
    })

    await setTutorials(false)
    await toggleDeveloperMode(false)

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
    const activeTagAfterReactivation = await browser.execute(() => {
      if (document.activeElement instanceof HTMLElement) document.activeElement.blur()
      return document.activeElement?.tagName ?? null
    })
    expect(activeTagAfterReactivation).toBe('BODY')
    await browser.keys('Backspace')
    await expect($('[data-pause]')).toBeDisplayed()
    expect(await browser.execute(() => document.activeElement?.tagName ?? null)).toBe('BODY')
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
    expectPersistedFormulaOrder('blank-sprout', REMEMBERED_FORMULA)
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
    expectPersistedBlankOrder(CREATED_ID)

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
    expectPersistedBlankOrder(CREATED_ID)

    await toggleDeveloperMode(true)
    await openLedger('orders')
    await expect(game()).toHaveAttribute('data-editor-state', 'create')
    await $('[data-order-editor-cancel]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    await $('[data-ledger-context="active"]').click()
    await $(`[data-order-id="${CREATED_ID}"]`).click()
    await expect(game()).toHaveAttribute('data-editor-state', 'edit')
    await $('[data-order-editor-delete]').click()
    await expect($('[data-order-editor]')).not.toBeDisplayed()
    await waitForSave()
    expect(storedOrderIds(slotId)).not.toContain(CREATED_ID)
    expect(persistedCatalog().some(({ id }) => id === CREATED_ID)).toBe(false)
    expect(await canvasCenterScreenshot()).not.toBe(acceptedPotFrame)
    await expect($(`[data-order-id="${CREATED_ID}"]`)).not.toExist()
    expect(await attribute('errors')).toBe('')
  })
})
