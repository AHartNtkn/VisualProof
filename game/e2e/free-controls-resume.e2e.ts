import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  attribute,
  canvas,
  displayedPose,
  expectPoseClose,
  game,
  hold,
  numberAttribute,
  rightClickWorld,
  storedTreeDiagram,
  waitForVisibleTreeTween,
} from './native'

describe('free-control recovery', () => {
  it('keeps an opened world and camera stable while controls pause and resume', async () => {
    await browser.execute(() => {
      const marker = '__ORCHARD_ORIGINAL_REQUEST_POINTER_LOCK__'
      Object.defineProperty(window, marker, {
        configurable: true,
        value: HTMLElement.prototype.requestPointerLock,
      })
      Object.defineProperty(HTMLElement.prototype, 'requestPointerLock', {
        configurable: true,
        value: () => Promise.reject(),
      })
    })

    await $('[data-load-slot="large-1"]').click()
    await browser.waitUntil(async () => (await attribute('ready')) === 'true' || (await attribute('errors')).length > 0, {
      timeout: 5_000,
      interval: 50,
      timeoutMsg: 'world neither opened nor reported an opening error',
    })
    await expect(game()).toHaveAttribute('data-ready', 'true')
    await expect(game()).toHaveAttribute('data-loaded-slot', 'large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect($('[data-reticle]')).not.toBeDisplayed()
    await expect($('[data-free-hint]')).not.toBeDisplayed()
    await expect($('[data-free-resume]')).toBeDisplayed()
    await expect($('[data-pointed]')).not.toBeDisplayed()

    const unavailablePose = await displayedPose()
    const unavailableDiagram = storedTreeDiagram('large-1', 'tree-0000')
    const settledBeforeUnavailableInput = await numberAttribute('settled-frame-samples')
    await hold('w')
    await canvas().moveTo({ xOffset: 40, yOffset: -25 })
    await rightClickWorld()
    await canvas().click()
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    expectPoseClose(await displayedPose(), unavailablePose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(unavailableDiagram)
    await browser.waitUntil(async () => await numberAttribute('settled-frame-samples') > settledBeforeUnavailableInput, {
      timeout: 2_000,
      interval: 50,
      timeoutMsg: 'render settlement stopped while free controls were unavailable',
    })

    await browser.execute(() => {
      const testWindow = window as Window & { __ORCHARD_ORIGINAL_REQUEST_POINTER_LOCK__?: typeof HTMLElement.prototype.requestPointerLock }
      const original = testWindow.__ORCHARD_ORIGINAL_REQUEST_POINTER_LOCK__
      if (typeof original !== 'function') throw new Error('missing original requestPointerLock')
      Object.defineProperty(HTMLElement.prototype, 'requestPointerLock', { configurable: true, value: original })
      delete testWindow.__ORCHARD_ORIGINAL_REQUEST_POINTER_LOCK__
    })
    await canvas().click()
    await browser.waitUntil(async () => await browser.execute(() => document.pointerLockElement?.hasAttribute('data-world') ?? false))
    await expect($('[data-reticle]')).toBeDisplayed()
    await expect($('[data-free-hint]')).toBeDisplayed()
    await expect($('[data-free-resume]')).not.toBeDisplayed()
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    expectPoseClose(await displayedPose(), unavailablePose)

    const beforeLoss = await displayedPose()
    await browser.execute(() => document.exitPointerLock())
    await browser.waitUntil(async () => await browser.execute(() => document.pointerLockElement === null))
    await expect(game()).toHaveAttribute('data-ready', 'true')
    await expect(game()).toHaveAttribute('data-loaded-slot', 'large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect($('[data-free-resume]')).toBeDisplayed()
    await expect($('[data-pointed]')).not.toBeDisplayed()
    expectPoseClose(await displayedPose(), beforeLoss)

    const diagramBeforeLostInput = storedTreeDiagram('large-1', 'tree-0000')
    const lostPose = await displayedPose()
    await hold('w')
    await canvas().moveTo({ xOffset: -30, yOffset: 25 })
    await rightClickWorld()
    expectPoseClose(await displayedPose(), lostPose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(diagramBeforeLostInput)

    await canvas().click()
    await browser.waitUntil(async () => await browser.execute(() => document.pointerLockElement?.hasAttribute('data-world') ?? false))
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    expectPoseClose(await displayedPose(), lostPose)

    const beforePersistedTool = storedTreeDiagram('large-1', 'tree-0000')
    const beforeToolPose = await displayedPose()
    await rightClickWorld()
    await waitForVisibleTreeTween()
    expect(storedTreeDiagram('large-1', 'tree-0000')).not.toEqual(beforePersistedTool)
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    expectPoseClose(await displayedPose(), beforeToolPose)
  })
})
