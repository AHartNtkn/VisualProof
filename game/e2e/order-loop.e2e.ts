import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import { Key } from 'webdriverio'
import {
  attribute,
  canvasScreenshot,
  clickWorld,
  createSlot,
  displayedPose,
  game,
  hold,
  rightClickWorld,
  storedOrder,
  storedReputation,
  storedTreeDiagram,
  storedTreeIds,
  waitForVisibleTreeTween,
} from './native'

const ORDER_ID = 'starter-double-cut'
const SOURCE_ID = 'tree-0000'

async function waitForSave(): Promise<void> {
  await expect(game()).toHaveAttribute('data-save-state', 'idle')
}

async function expectTextContains(selector: string, expected: string): Promise<void> {
  await browser.waitUntil(async () => (await $(selector).getText()).includes(expected), {
    timeoutMsg: `${selector} did not contain ${JSON.stringify(expected)}`,
  })
}

async function moveFreeCameraTo(
  target: { readonly x: number; readonly y: number; readonly z: number },
): Promise<void> {
  const moveAxis = async (
    axis: 'x' | 'y' | 'z',
    positive: string,
    negative: string,
  ): Promise<void> => {
    for (let attempt = 0; attempt < 10; attempt++) {
      const delta = target[axis] - (await displayedPose()).eye[axis]
      if (Math.abs(delta) < 0.08) return
      await hold(delta > 0 ? positive : negative, Math.max(12, Math.round(Math.abs(delta) * 125)))
    }
    expect(Math.abs((await displayedPose()).eye[axis] - target[axis])).toBeLessThan(0.1)
  }
  await moveAxis('x', 'd', 'a')
  await moveAxis('z', 's', 'w')
  await moveAxis('y', Key.Space, Key.Control)
}

async function aimReticleAt(
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
}

async function soleSlotId(): Promise<string> {
  const load = $('[data-load-slot]')
  await load.waitForDisplayed()
  const slotId = await load.getAttribute('data-load-slot')
  if (slotId === null || slotId.length === 0) throw new Error('expected one saved orchard')
  return slotId
}

async function expectPlaying(
  state: {
    readonly mode?: 'free' | 'orbit'
    readonly engaged?: boolean
    readonly item?: 'double-cut' | 'iteration'
    readonly cutting?: boolean
    readonly catalog?: boolean
    readonly order?: 'pending' | 'accepted' | 'completed'
    readonly reputation?: number
  },
): Promise<void> {
  if (state.mode !== undefined) await expect(game()).toHaveAttribute('data-camera-mode', state.mode)
  if (state.engaged !== undefined) {
    await expect(game()).toHaveAttribute('data-input-engaged', String(state.engaged))
  }
  if (state.item !== undefined) await expect(game()).toHaveAttribute('data-equipped-item', state.item)
  if (state.cutting !== undefined) {
    await expect(game()).toHaveAttribute('data-cutting-held', String(state.cutting))
  }
  if (state.catalog !== undefined) {
    await expect(game()).toHaveAttribute('data-catalog-open', String(state.catalog))
  }
  if (state.order !== undefined) await expect(game()).toHaveAttribute('data-order-state', state.order)
  if (state.reputation !== undefined) {
    await expect(game()).toHaveAttribute('data-reputation', String(state.reputation))
  }
}

async function openCatalog(): Promise<void> {
  await browser.keys('Tab')
  await expect($('[data-catalog]')).toBeDisplayed()
  await expectPlaying({ mode: 'free', engaged: false, catalog: true })
}

describe('orchard first order loop', () => {
  const phase = process.env['GAME_E2E_PHASE']

  it('plays or reloads the order loop through native controls', async () => {
    if (phase === 'play') {
      const slotId = await createSlot('Order Loop')
      await expectPlaying({
        mode: 'free', engaged: true, item: 'double-cut', cutting: false,
        catalog: false, order: 'pending', reputation: 0,
      })

      const beforeMove = await displayedPose()
      await hold('w', 120)
      const movedView = await displayedPose()
      expect(movedView.eye).not.toEqual(beforeMove.eye)
      await clickWorld()
      await expectPlaying({ mode: 'orbit', engaged: false })
      const beforeLook = await displayedPose()
      await hold('a', 120)
      expect((await displayedPose()).direction).not.toEqual(beforeLook.direction)
      await browser.keys('Escape')
      await expectPlaying({ mode: 'free', engaged: true })
      await hold('d', 260)
      const chosenView = await displayedPose()

      await openCatalog()
      await expect($(`[data-catalog-accept="${ORDER_ID}"]`)).toBeDisplayed()
      await $(`[data-catalog-accept="${ORDER_ID}"]`).click()
      await expect($('[data-catalog]')).not.toBeDisplayed()
      await expect($('[data-feedback]')).toHaveText(`Accepted ${ORDER_ID}.`)
      await expectPlaying({
        mode: 'free', engaged: true, item: 'double-cut', cutting: false,
        catalog: false, order: 'accepted', reputation: 0,
      })
      await waitForSave()

      const accepted = storedOrder(slotId, ORDER_ID)
      expect(accepted.state).toBe('accepted')
      expect(accepted.pot).not.toBeNull()
      const horizontalLength = Math.hypot(chosenView.direction.x, chosenView.direction.z)
      const expectedX = chosenView.eye.x + (chosenView.direction.x / horizontalLength) * 6
      const expectedZ = chosenView.eye.z + (chosenView.direction.z / horizontalLength) * 6
      expect(accepted.pot!.x).toBeCloseTo(expectedX, 6)
      expect(accepted.pot!.z).toBeCloseTo(expectedZ, 6)
      expect(Math.hypot(accepted.pot!.x - chosenView.eye.x, accepted.pot!.z - chosenView.eye.z))
        .toBeCloseTo(6, 6)
      expect(storedTreeIds(slotId)).toEqual([SOURCE_ID])
      expect(storedReputation(slotId)).toBe(0)
      return
    }

    if (phase !== 'reload') throw new Error(`unknown order-loop phase '${String(phase)}'`)

    const slotId = await soleSlotId()
    await $(`[data-load-slot="${slotId}"]`).click()
    await expectPlaying({
      mode: 'free', engaged: true, item: 'double-cut', cutting: false,
      catalog: false, order: 'accepted', reputation: 0,
    })
    expect(storedOrder(slotId, ORDER_ID).state).toBe('accepted')
    expect(storedOrder(slotId, ORDER_ID).pot).not.toBeNull()
    const acceptedPot = storedOrder(slotId, ORDER_ID).pot
    if (acceptedPot === null) throw new Error('accepted order did not retain its pot')
    const sourceBefore = storedTreeDiagram(slotId, SOURCE_ID)
    await aimReticleAt({ x: 0, y: 0.25, z: 0 })

    await browser.keys('1')
    await expect($('[data-feedback]')).toHaveText('Equipped Iteration.')
    await expectPlaying({ item: 'iteration', cutting: false })

    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Whole-tree cutting held from ${SOURCE_ID}.`)
    await expectPlaying({ mode: 'free', engaged: true, item: 'iteration', cutting: true })
    const duplicateGround = { x: -4, z: 0 }
    await aimReticleAt({ ...duplicateGround, y: -0.035 })
    const duplicateDirection = (await displayedPose()).direction
    const duplicateYaw = Math.atan2(-duplicateDirection.x, -duplicateDirection.z)
    const beforeDuplicateFrame = await canvasScreenshot()
    await rightClickWorld()
    await expectTextContains('[data-feedback]', 'Duplicated tree as tree-')
    await waitForVisibleTreeTween(beforeDuplicateFrame)
    await expectPlaying({ mode: 'free', engaged: true, item: 'iteration', cutting: false })
    const idsAfterDuplicate = storedTreeIds(slotId)
    expect(idsAfterDuplicate).toHaveLength(2)
    expect(idsAfterDuplicate).toContain(SOURCE_ID)
    const duplicateId = idsAfterDuplicate.find((id) => id !== SOURCE_ID)
    if (duplicateId === undefined) throw new Error('duplicate did not receive a fresh tree ID')
    expect(storedTreeDiagram(slotId, SOURCE_ID)).toEqual(sourceBefore)

    await browser.keys('1')
    await expect($('[data-feedback]')).toHaveText('Equipped Double Cut.')
    await expectPlaying({ item: 'double-cut', cutting: false })
    const duplicateBeforeCut = storedTreeDiagram(slotId, duplicateId)
    await aimReticleAt({ ...duplicateGround, y: 0.25 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Double cut applied to ${duplicateId}.`)
    await waitForVisibleTreeTween()
    const duplicateAfterCut = storedTreeDiagram(slotId, duplicateId)
    expect(Object.keys(duplicateAfterCut.regions)).toHaveLength(
      Object.keys(duplicateBeforeCut.regions).length + 2,
    )

    await browser.keys('1')
    await expectPlaying({ item: 'iteration', cutting: false })

    await aimReticleAt({ ...duplicateGround, y: 1.05 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Subtree cutting held from ${duplicateId}.`)
    await expectPlaying({ mode: 'free', item: 'iteration', cutting: true })
    await aimReticleAt({ ...duplicateGround, y: 0.25 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Iteration applied to ${duplicateId}.`)
    await waitForVisibleTreeTween()
    await expectPlaying({ item: 'iteration', cutting: false })
    const duplicateAfterIteration = storedTreeDiagram(slotId, duplicateId)
    expect(Object.keys(duplicateAfterIteration.regions).length)
      .toBeGreaterThan(Object.keys(duplicateAfterCut.regions).length)

    const branchLocal = { x: 0.155, z: -0.343 }
    const cosine = Math.cos(duplicateYaw)
    const sine = Math.sin(duplicateYaw)
    await aimReticleAt({
      x: duplicateGround.x + branchLocal.x * cosine + branchLocal.z * sine,
      y: 1.05,
      z: duplicateGround.z - branchLocal.x * sine + branchLocal.z * cosine,
    })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Subtree cutting held from ${duplicateId}.`)
    await expectPlaying({ mode: 'free', item: 'iteration', cutting: true })
    await aimReticleAt({ x: 0, y: 0.25, z: 0 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText('cross-tree iteration requires a whole tree cutting')
    await expectPlaying({ mode: 'free', item: 'iteration', cutting: true, order: 'accepted', reputation: 0 })
    expect(storedTreeDiagram(slotId, SOURCE_ID)).toEqual(sourceBefore)

    await browser.keys('Escape')
    await expect($('[data-feedback]')).toHaveText('Cutting cleared.')
    await expectPlaying({ mode: 'free', engaged: true, item: 'iteration', cutting: false })

    await aimReticleAt({ ...duplicateGround, y: 0.25 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Whole-tree cutting held from ${duplicateId}.`)
    await aimReticleAt({ x: acceptedPot.x + 0.85, y: 0.55, z: acceptedPot.z })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`delivered proposition does not match order '${ORDER_ID}'`)
    await expectPlaying({ mode: 'free', item: 'iteration', cutting: true, order: 'accepted', reputation: 0 })
    expect(storedOrder(slotId, ORDER_ID).state).toBe('accepted')
    expect(storedReputation(slotId)).toBe(0)
    expect(storedTreeIds(slotId)).toEqual(idsAfterDuplicate)
    expect(storedTreeDiagram(slotId, SOURCE_ID)).toEqual(sourceBefore)

    await browser.keys('Escape')
    await expect($('[data-feedback]')).toHaveText('Cutting cleared.')
    await expectPlaying({ mode: 'free', engaged: true, item: 'iteration', cutting: false })
    await browser.keys('1')
    await expectPlaying({ item: 'double-cut', cutting: false })
    await aimReticleAt({ x: 0, y: 0.25, z: 0 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Double cut applied to ${SOURCE_ID}.`)
    await waitForVisibleTreeTween()
    const exactSource = storedTreeDiagram(slotId, SOURCE_ID)
    expect(Object.keys(exactSource.regions)).toHaveLength(Object.keys(sourceBefore.regions).length + 2)

    await browser.keys('1')
    await aimReticleAt({ x: 0, y: 0.25, z: 0 })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Whole-tree cutting held from ${SOURCE_ID}.`)
    await aimReticleAt({ x: acceptedPot.x + 0.85, y: 0.55, z: acceptedPot.z })
    await rightClickWorld()
    await expect($('[data-feedback]')).toHaveText(`Completed ${ORDER_ID}. Reputation 1.`)
    await expectPlaying({ item: 'iteration', cutting: false, order: 'completed', reputation: 1 })
    await waitForSave()
    expect(storedOrder(slotId, ORDER_ID)).toEqual({ state: 'completed', pot: null })
    expect(storedReputation(slotId)).toBe(1)
    expect(storedTreeIds(slotId)).toEqual(idsAfterDuplicate)
    expect(storedTreeDiagram(slotId, SOURCE_ID)).toEqual(exactSource)

    await openCatalog()
    await $('[data-catalog-completed]').click()
    await expect($('[data-catalog-completed]')).toHaveAttribute('aria-pressed', 'true')
    await expect($('[data-catalog-pending]')).toHaveAttribute('aria-pressed', 'false')
    await expect($('[data-catalog-orders] strong')).toHaveText('Double Cut')
    await expect($('[data-catalog-reputation]')).toHaveText('Reputation: 1')
    await browser.keys('Escape')
    await expectPlaying({ catalog: false, mode: 'free', order: 'completed', reputation: 1 })

    await browser.refresh()
    const reloadedSlotId = await soleSlotId()
    expect(reloadedSlotId).toBe(slotId)
    await $(`[data-load-slot="${slotId}"]`).click()
    await expectPlaying({
      mode: 'free', engaged: true, item: 'double-cut', cutting: false,
      catalog: false, order: 'completed', reputation: 1,
    })
    expect(storedOrder(slotId, ORDER_ID)).toEqual({ state: 'completed', pot: null })
    expect(storedReputation(slotId)).toBe(1)
    expect(storedTreeIds(slotId)).toEqual(idsAfterDuplicate)
    expect(storedTreeDiagram(slotId, SOURCE_ID)).toEqual(exactSource)
    expect(await attribute('errors')).toBe('')
  })
})
