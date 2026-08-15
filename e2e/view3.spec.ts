import { expect } from '@playwright/test'
import { test } from './zero-signature-fixture'

test('3D view mounts, renders the trunk, reports hover, and unmounts', async ({ page }) => {
  await page.goto('/')
  await page.getByRole('button', { name: 'Utilities' }).click()
  await page.getByRole('button', { name: '3D view' }).click()

  const canvas3 = page.locator('canvas[data-view3]')
  await expect(canvas3).toBeVisible()
  await expect(page.locator('#c')).toBeHidden()

  // Rendered content: count pixels that differ from the background.
  // (render.ts sets preserveDrawingBuffer so the buffer is readable.)
  await page.waitForTimeout(300)
  const inkCount = await canvas3.evaluate((c) => {
    const el = c as HTMLCanvasElement
    const off = document.createElement('canvas')
    off.width = el.width
    off.height = el.height
    const ctx = off.getContext('2d')
    if (ctx === null) throw new Error('no 2d context for readback')
    ctx.drawImage(el, 0, 0)
    const img = ctx.getImageData(0, 0, off.width, off.height).data
    const bg = [img[0], img[1], img[2]] as const
    let n = 0
    for (let i = 0; i < img.length; i += 4) {
      const dr = Math.abs(img[i]! - bg[0]!) + Math.abs(img[i + 1]! - bg[1]!) + Math.abs(img[i + 2]! - bg[2]!)
      if (dr > 30) n++
    }
    return n
  })
  expect(inkCount).toBeGreaterThan(50)

  // Hover: the empty sheet's trunk is a vertical line through the view center.
  const box = (await canvas3.boundingBox())!
  const wrap = page.locator('div[data-view3-hover]')
  let hover = ''
  for (let f = 0.25; f <= 0.75 && hover === ''; f += 0.05) {
    await page.mouse.move(box.x + box.width / 2, box.y + box.height * f)
    await page.waitForTimeout(50)
    hover = (await wrap.getAttribute('data-view3-hover')) ?? ''
  }
  expect(hover).toMatch(/^b:/)

  // Toggle back.
  await page.getByRole('button', { name: '2D view' }).click()
  await expect(page.locator('canvas[data-view3]')).toHaveCount(0)
  await expect(page.locator('#c')).toBeVisible()
})
