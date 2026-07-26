import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      interaction(): {
        selected: readonly { kind: 'node' | 'region' | 'wire'; id: string }[]
        pins: string[]
        userZoom: number
      }
    }
  }
}

test('a modified background drag leaves an empty structural workspace unchanged', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const canvas = await page.locator('#c').boundingBox()
  if (canvas === null) throw new Error('the main canvas has no bounding box')

  const before = await page.evaluate(() => ({
    nodes: window.__vpaDebug!.nodeCount(),
    status: window.__vpaDebug!.status(),
    interaction: window.__vpaDebug!.interaction(),
  }))

  await page.keyboard.down('Control')
  await page.mouse.move(canvas.x + canvas.width * 0.35, canvas.y + canvas.height * 0.45)
  await page.mouse.down()
  await page.mouse.move(canvas.x + canvas.width * 0.65, canvas.y + canvas.height * 0.55)
  await page.mouse.up()
  await page.keyboard.up('Control')

  expect(await page.evaluate(() => ({
    nodes: window.__vpaDebug!.nodeCount(),
    status: window.__vpaDebug!.status(),
    interaction: window.__vpaDebug!.interaction(),
  }))).toEqual(before)
})
