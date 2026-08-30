import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  clickWorld,
  displayedPose,
  expectPoseClose,
  game,
  hold,
  loadSlot,
  poseEyeDistance,
  storedCameraPose,
  waitForMenu,
} from './native'

async function openPauseAndResume(expected: {
  readonly mode: 'free' | 'orbit'
  readonly ledgerOpen: boolean
}): Promise<void> {
  const pose = await displayedPose()
  await browser.keys('Escape')
  await expect(game()).toHaveAttribute('data-paused', 'true')
  await expect($('[data-pause]')).toBeDisplayed()
  await expect($('[data-pause-resume]')).toBeFocused()
  await expect(game()).toHaveAttribute('data-camera-mode', expected.mode)
  await expect(game()).toHaveAttribute('data-ledger-open', String(expected.ledgerOpen))
  await expectPoseClose(await displayedPose(), pose)

  await $('[data-pause-resume]').click()
  await expect($('[data-pause]')).not.toBeDisplayed()
  await expect(game()).toHaveAttribute('data-paused', 'false')
  await expect(game()).toHaveAttribute('data-camera-mode', expected.mode)
  await expect(game()).toHaveAttribute('data-ledger-open', String(expected.ledgerOpen))
  await expectPoseClose(await displayedPose(), pose)
}

describe('orchard world controls', () => {
  it('preserves free flight, orbit, and ledger states across Pause and uses Backspace to step back', async () => {
    await waitForMenu()
    await expect($('.slot.invalid')).toBeDisplayed()
    await expect($('.slot.invalid small')).not.toHaveText('')
    await $('[data-new-slot-name]').setValue('   ')
    await $('[data-create-slot]').click()
    await expect($('[data-menu-error]')).toHaveText('Enter a name for the new orchard.')

    await loadSlot('large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await expect(game()).toHaveAttribute('data-acquired-tool-ids', '["sprout-spawner"]')
    await expect(game()).toHaveAttribute('data-selected-tool', 'sprout-spawner')
    await expect($('.tool-selector-category')).not.toExist()
    await expect($('.tool-selector-row')).not.toExist()
    expect(await game().getText()).not.toContain('Sprout Spawner')

    const loadedPose = await displayedPose()
    await hold('w')
    const movedPose = await displayedPose()
    expect(poseEyeDistance(movedPose, loadedPose)).toBeGreaterThan(0.01)
    await browser.waitUntil(() => poseEyeDistance(storedCameraPose('large-1'), movedPose) < 0.000_001)

    await openPauseAndResume({ mode: 'free', ledgerOpen: false })
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')

    await browser.keys('Tab')
    await expect($('[data-ledger]')).toBeDisplayed()
    await expect(game()).toHaveAttribute('data-ledger-open', 'true')
    await expect(game()).toHaveAttribute('data-ledger-tab', 'tools')
    await openPauseAndResume({ mode: 'free', ledgerOpen: true })
    await expect($('[data-ledger]')).toBeDisplayed()
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    await browser.keys('Tab')
    await expect($('[data-ledger]')).not.toBeDisplayed()
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')

    await clickWorld()
    await expect(game()).toHaveAttribute('data-camera-mode', 'orbit')
    await expect(game()).toHaveAttribute('data-orbit-target', 'tree-0000')
    const orbitPose = await displayedPose()
    await hold('a')
    expect(poseEyeDistance(await displayedPose(), orbitPose)).toBeGreaterThan(0.01)
    expectPoseClose(storedCameraPose('large-1'), movedPose)

    await openPauseAndResume({ mode: 'orbit', ledgerOpen: false })
    await expect(game()).toHaveAttribute('data-input-engaged', 'false')
    await browser.keys('Backspace')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect(game()).toHaveAttribute('data-input-engaged', 'true')
    await expectPoseClose(await displayedPose(), movedPose)

    await browser.keys('1')
    await expect(game()).toHaveAttribute('data-selected-tool', 'sprout-spawner')
    await expect(game()).toHaveAttribute('data-selector-visible', 'true')
    await expect($('[data-tool-selector]')).toBeDisplayed()
    await expect($('.tool-selector-category')).toHaveText('1')
    await expect($('.tool-selector-row')).toHaveText('Sprout Spawner')
    await browser.waitUntil(async () => await game().getAttribute('data-selector-visible') === 'false', {
      timeout: 3_000,
      timeoutMsg: 'single acquired-tool selector did not fade',
    })
    await expect($('.tool-selector-category')).not.toExist()
    await expect($('.tool-selector-row')).not.toExist()
    expect(await game().getText()).not.toContain('Sprout Spawner')

    await browser.keys('Escape')
    await $('[data-pause-main-menu]').click()
    await waitForMenu()
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    await loadSlot('large-1')
    await expectPoseClose(await displayedPose(), movedPose)
  })
})
