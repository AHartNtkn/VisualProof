import { $, browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import {
  attribute,
  canvas,
  game,
  hold,
  loadSlot,
  rightClickWorld,
  storedTreeDiagram,
} from './native'

describe('unexpected Pointer Lock loss', () => {
  it('stops mounted-world input and clears free-flight control presentation', async () => {
    await loadSlot('large-1')
    await expect(game()).toHaveAttribute('data-camera-mode', 'free')
    await expect($('[data-free-hint]')).toBeDisplayed()
    await expect($('[data-reticle]')).toBeDisplayed()

    const pointed = $('[data-pointed]')
    await browser.waitUntil(async () => (await pointed.getText()).length > 0)
    await expect(pointed).toBeDisplayed()
    expect(await game().getAttribute('class')).toContain('has-pointed')
    const beforeLoss = storedTreeDiagram('large-1', 'tree-0000')

    expect(await browser.execute(() => document.pointerLockElement?.hasAttribute('data-world') ?? false)).toBe(true)
    await browser.execute(() => document.exitPointerLock())
    await browser.waitUntil(async () => await browser.execute(() => document.pointerLockElement === null))

    await expect(game()).toHaveAttribute('data-errors', 'Pointer Lock was lost; free look stopped.')
    for (const name of ['camera-mode', 'displayed-eye', 'displayed-direction', 'orbit-target']) {
      expect(await attribute(name)).toBe('')
    }
    await expect($('[data-free-hint]')).not.toBeDisplayed()
    await expect($('[data-orbit-hint]')).not.toBeDisplayed()
    await expect($('[data-reticle]')).not.toBeDisplayed()
    await expect(pointed).not.toBeDisplayed()
    expect(await pointed.getText()).toBe('')
    expect(await game().getAttribute('class')).not.toContain('has-pointed')

    await hold('w')
    await canvas().moveTo({ xOffset: 40, yOffset: -25 })
    await canvas().click()
    await rightClickWorld()

    for (const name of ['camera-mode', 'displayed-eye', 'displayed-direction', 'orbit-target']) {
      expect(await attribute(name)).toBe('')
    }
    expect(storedTreeDiagram('large-1', 'tree-0000')).toEqual(beforeLoss)
    await expect(game()).toHaveAttribute('data-errors', 'Pointer Lock was lost; free look stopped.')
  })
})
