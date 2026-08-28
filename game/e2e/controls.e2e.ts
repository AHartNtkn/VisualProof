import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  canvas,
  clickWorld,
  displayedPose,
  expectDirectionClose,
  expectEyeClose,
  expectPoseClose,
  game,
  hold,
  movePointer,
  poseDirectionDistance,
  poseEyeDistance,
  rightClickWorld,
  storedCameraPose,
  storedTreeDiagram,
} from './native'

describe('orchard world controls', () => {
  it('moves through free flight and orbit while persisting only the free pose', async () => {
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    await expect($('.slot.invalid')).toBeDisplayed()
    await expect($('.slot.invalid small')).not.toHaveText('')
    await $('[data-new-slot-name]').setValue('   ')
    await $('[data-create-slot]').click()
    await expect($('[data-menu-error]')).toHaveText('Enter a name for the new orchard.')

    await $('[data-load-slot="large-1"]').click()
    await expect(game()).toHaveAttribute('data-ready', 'true')
    await expect(game()).toHaveAttribute('data-loaded-slot', 'large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    const engagePrompt = $('[data-engage]')
    await expect(engagePrompt).toBeDisplayed()
    await expect(engagePrompt).toHaveText('Click to play')
    const [promptLocation, promptSize, canvasLocation, canvasSize] = await Promise.all([
      engagePrompt.getLocation(),
      engagePrompt.getSize(),
      canvas().getLocation(),
      canvas().getSize(),
    ])
    expect(promptLocation.x + promptSize.width / 2)
      .toBeCloseTo(canvasLocation.x + canvasSize.width / 2, 0)
    expect(promptLocation.y + promptSize.height / 2)
      .toBeCloseTo(canvasLocation.y + canvasSize.height / 2, 0)
    await expect($('[data-reticle]')).not.toBeDisplayed()

    const loadedPose = await displayedPose()
    await clickWorld()
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await expectPoseClose(await displayedPose(), loadedPose)
    await expect($('[data-reticle]')).toBeDisplayed()
    await expect($('[data-engage]')).not.toBeDisplayed()

    await hold('w')
    const movedPose = await displayedPose()
    expect(poseEyeDistance(movedPose, loadedPose)).toBeGreaterThan(0.01)
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')

    await movePointer(12, -8)
    await browser.waitUntil(async () => poseDirectionDistance(await displayedPose(), movedPose) > 0.001)
    const preOrbitPose = await displayedPose()
    expectEyeClose(preOrbitPose, movedPose)

    await browser.waitUntil(() => poseEyeDistance(storedCameraPose('large-1'), preOrbitPose) < 0.000_001)
    await expect(game()).toHaveAttribute('data-save-state', 'idle')
    const storedDiagram = storedTreeDiagram('large-1', 'tree-0000')
    await clickWorld()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    await expect($('[data-reticle]')).not.toBeDisplayed()
    await expect($('[data-engage]')).not.toBeDisplayed()
    expect((await canvas().getCSSProperty('cursor')).value).toBe('auto')
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(storedDiagram)

    const orbitPose = await displayedPose()
    await movePointer(40, 25)
    await browser.pause(100)
    await expectPoseClose(await displayedPose(), orbitPose)

    const savedFreePose = storedCameraPose('large-1')
    await hold('a')
    const movedOrbitPose = await displayedPose()
    expect(poseEyeDistance(movedOrbitPose, orbitPose)).toBeGreaterThan(0.01)
    expectPoseClose(storedCameraPose('large-1'), savedFreePose)

    await rightClickWorld()
    await browser.pause(100)
    await expectPoseClose(await displayedPose(), movedOrbitPose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(storedDiagram)

    await browser.keys('Escape')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    await expectPoseClose(await displayedPose(), preOrbitPose)

    await clickWorld()
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await hold('w')
    const finalPose = await displayedPose()
    expect(poseEyeDistance(finalPose, preOrbitPose)).toBeGreaterThan(0.01)
    expectDirectionClose(finalPose, preOrbitPose)
    await browser.waitUntil(() => poseEyeDistance(storedCameraPose('large-1'), finalPose) < 0.000_001)
    await expect(game()).toHaveAttribute('data-save-state', 'idle')
    await expectPoseClose(storedCameraPose('large-1'), finalPose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(storedDiagram)
  })
})
