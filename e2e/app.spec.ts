import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: { nodeCount(): number; status(): string }
  }
}

test('the app boots with both theories loaded', async ({ page }) => {
  await page.goto('/?debug')
  await expect(page.locator('canvas')).toBeVisible()
  await expect(page.locator('#theorems')).toContainText('onePlusOne')
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status.toLowerCase()).toContain('edit')
})

test('term entry adds a node to the edit diagram', async ({ page }) => {
  await page.goto('/?debug')
  const before = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  const after = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(after).toBe(before + 1)
})

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  // build lhs: one identity node; snapshot as lhs
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  // set rhs = same diagram, prove with zero steps (met immediately)
  await page.getByRole('button', { name: /set goal rhs/i }).click()
  await page.getByRole('button', { name: /switch to prove/i }).click()
  await page.getByRole('button', { name: /assemble/i }).click()
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status).toMatch(/assembled|checked|adopted/i)
})
