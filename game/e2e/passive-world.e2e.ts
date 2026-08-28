import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  canvas,
  displayedPose,
  expectPoseClose,
  game,
  hold,
  rightClickWorld,
  storedTreeDiagram,
} from './native'

describe('passive orchard world', () => {
  it('renders a loaded save without exposing or responding to in-world controls', async () => {
    await expect(game()).toHaveAttribute('data-camera-mode', 'menu')
    await expect($('.slot.invalid')).toBeDisplayed()
    await expect($('.slot.invalid small')).not.toHaveText('')
    await $('[data-new-slot-name]').setValue('   ')
    await $('[data-create-slot]').click()
    await expect($('[data-menu-error]')).toHaveText('Enter a name for the new orchard.')

    await $('[data-load-slot="large-1"]').click()
    await expect(game()).toHaveAttribute('data-ready', 'true')
    await expect(game()).toHaveAttribute('data-loaded-slot', 'large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'fixed')

    for (const selector of [
      '[data-reticle]',
      '[data-free-hint]',
      '[data-free-resume]',
      '[data-orbit-hint]',
      '[data-pointed]',
    ]) expect(await $(selector).isExisting()).toBe(false)

    const pose = await displayedPose()
    const diagram = storedTreeDiagram('large-1', 'tree-0000')
    await hold('w')
    await hold('a')
    await canvas().moveTo({ xOffset: 60, yOffset: 35 })
    await canvas().click()
    await rightClickWorld()
    await browser.keys('Escape')

    expectPoseClose(await displayedPose(), pose)
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(diagram)
    await expect(game()).toHaveAttribute('data-camera-mode', 'fixed')
    await expect(game()).toHaveAttribute('data-save-state', 'idle')
  })
})
