import { writeFileSync } from 'node:fs'
import { join } from 'node:path'
import { $, browser, expect } from '@wdio/globals'
import { Key } from 'webdriverio'
import { describe, it } from 'mocha'
import {
  attribute,
  canvas,
  createSlot,
  displayedPose,
  expectDoubleCut,
  expectPoseClose,
  game,
  hold,
  holdTogether,
  movePrivatePointerOutsideWindow,
  movePrivatePointerTowardOrigin,
  pointerIsInsideOrchard,
  pressEscape,
  privatePointerLocation,
  resizeAndMoveOrchard,
  rightClickWorld,
  settledDisplayedPose,
  storedTreeDiagram,
  waitForVisibleTreeTween,
} from './native'

const receiptPath = join(process.env['GAME_E2E_DATA_ROOT'] ?? '', 'double-cut.json')

describe('native camera and reach behavior', () => {
  it('flies under native capture, orbits a nearby tree, and rejects distant interaction', async () => {
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    await expect($('.slot.invalid')).toBeDisplayed()
    await expect($('.slot.invalid small')).not.toHaveText('')
    const menuTarget = movePrivatePointerOutsideWindow()
    expect(privatePointerLocation()).toEqual(menuTarget)
    await $('[data-new-slot-name]').setValue('   ')
    await $('[data-create-slot]').click()
    await expect($('[data-menu-error]')).toHaveText('Enter a name for the new orchard.')
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    expect(privatePointerLocation()).toEqual(menuTarget)
    const seedlingSlot = await createSlot('Camera Orchard')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    const seedlingBefore = storedTreeDiagram(seedlingSlot, 'tree-0000')
    const toolPose = await displayedPose()
    await rightClickWorld()
    await waitForVisibleTreeTween()
    const seedlingAfter = storedTreeDiagram(seedlingSlot, 'tree-0000')
    expectDoubleCut(seedlingBefore, seedlingAfter, seedlingBefore.root)
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-orbit-target', '')
    expectPoseClose(await displayedPose(), toolPose)
    writeFileSync(receiptPath, JSON.stringify({ seedlingSlot, seedlingAfter }))

    await canvas().click()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')

    const beforeOrbitMouse = await displayedPose()
    const orbitTarget = movePrivatePointerOutsideWindow()
    expect(privatePointerLocation()).toEqual(orbitTarget)
    expectPoseClose(await displayedPose(), beforeOrbitMouse)

    const beforeA = await displayedPose()
    await hold('a')
    const afterA = await displayedPose()
    expect(afterA.eye.x).toBeLessThan(beforeA.eye.x)
    expect(afterA.direction.x).not.toBeCloseTo(beforeA.direction.x, 7)
    const beforeD = afterA
    await hold('d')
    const afterD = await displayedPose()
    expect(afterD.eye.x).toBeGreaterThan(beforeD.eye.x)
    expect(afterD.direction.x).not.toBeCloseTo(beforeD.direction.x, 7)

    const beforeW = await displayedPose()
    await hold('w')
    const afterW = await displayedPose()
    const wDelta = {
      x: afterW.eye.x - beforeW.eye.x,
      y: afterW.eye.y - beforeW.eye.y,
      z: afterW.eye.z - beforeW.eye.z,
    }
    expect(wDelta.x * beforeW.direction.x + wDelta.y * beforeW.direction.y + wDelta.z * beforeW.direction.z)
      .toBeGreaterThan(0)
    const beforeS = afterW
    await hold('s')
    const afterS = await displayedPose()
    const sDelta = {
      x: afterS.eye.x - beforeS.eye.x,
      y: afterS.eye.y - beforeS.eye.y,
      z: afterS.eye.z - beforeS.eye.z,
    }
    expect(sDelta.x * beforeS.direction.x + sDelta.y * beforeS.direction.y + sDelta.z * beforeS.direction.z)
      .toBeLessThan(0)

    const beforeControl = await displayedPose()
    await hold(Key.Ctrl)
    const afterControl = await displayedPose()
    expect(afterControl.eye.y).toBeLessThan(beforeControl.eye.y)
    const beforeSpace = afterControl
    await hold(Key.Space)
    expect((await displayedPose()).eye.y).toBeGreaterThan(beforeSpace.eye.y)

    const beforeExit = await settledDisplayedPose()
    await pressEscape()
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-orbit-target', '')
    expectPoseClose(await displayedPose(), beforeExit)
    movePrivatePointerOutsideWindow()
    expect(pointerIsInsideOrchard(privatePointerLocation())).toBe(true)

    const beforeMouse = await displayedPose()
    await canvas().moveTo({ xOffset: 60, yOffset: 35 })
    await browser.waitUntil(async () => JSON.stringify(await displayedPose()) !== JSON.stringify(beforeMouse))

    await holdTogether([Key.Shift, 's'], 7_000)
    const farPose = await displayedPose()
    await canvas().click()
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    expectPoseClose(await displayedPose(), farPose)
    const farDiagram = storedTreeDiagram(seedlingSlot, 'tree-0000')
    await rightClickWorld()
    await browser.waitUntil(async () => (await attribute('errors')).includes('within reach'))
    expect(storedTreeDiagram(seedlingSlot, 'tree-0000')).toEqual(farDiagram)
    expectPoseClose(await displayedPose(), farPose)

    const beforeWindowChange = await displayedPose()
    const movedWindow = resizeAndMoveOrchard(700, 500, 800, 400)
    expect(movedWindow).toEqual({ x: 800, y: 400, width: 700, height: 500 })
    await browser.waitUntil(async () => pointerIsInsideOrchard(privatePointerLocation()), {
      interval: 50,
      timeout: 2_000,
      timeoutMsg: 'pointer was not recentered inside resized/moved Orchard window',
    })
    await browser.pause(200)
    expectPoseClose(await displayedPose(), beforeWindowChange)
    movePrivatePointerTowardOrigin()
    const confinedAfterMove = privatePointerLocation()
    if (!pointerIsInsideOrchard(confinedAfterMove)) {
      throw new Error(`pointer crossed resized/moved Orchard boundary: ${JSON.stringify({ movedWindow, confinedAfterMove })}`)
    }
  })
})
