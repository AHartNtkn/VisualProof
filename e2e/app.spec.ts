import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: { nodeCount(): number; status(): string }
  }
}

test('the app boots empty and loads a theory on demand', async ({ page }) => {
  await page.goto('/?debug')
  await expect(page.locator('canvas')).toBeVisible()
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const lib = page.locator('#library')
  // The Library panel lists the available files; nothing is loaded at boot, so
  // no theory content is on screen yet.
  await expect(lib.getByRole('button', { name: 'Load frege.json', exact: true })).toBeVisible()
  await expect(lib.getByRole('button', { name: 'Load lambda.json', exact: true })).toBeVisible()
  await expect(lib).not.toContainText('plusAssoc')

  // Load frege explicitly, then open its detail group — the theorems appear.
  await lib.getByRole('button', { name: 'Load frege.json', exact: true }).click()
  await expect(lib.getByRole('button', { name: 'Unload frege.json', exact: true })).toBeVisible()
  await lib.getByRole('button', { name: '▸ frege.json', exact: true }).click()
  await expect(lib).toContainText('plusAssoc')

  // Unloading removes the theory content again; the sheet is unaffected.
  await lib.getByRole('button', { name: 'Unload frege.json', exact: true }).click()
  await expect(lib).not.toContainText('plusAssoc')
  await expect(lib.getByRole('button', { name: 'Load frege.json', exact: true })).toBeVisible()

  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status.toLowerCase()).toContain('edit')
})

test('term entry adds a node to the edit diagram', async ({ page }) => {
  await page.goto('/?debug')
  // Boot fetches the manifest asynchronously; the debug seam is installed only
  // once the mount completes. Wait for it before reading node counts.
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  const before = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  const after = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(after).toBe(before + 1)
})

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  // build lhs: one identity node; snapshot as lhs (no citations, so this proves
  // against the empty boot context)
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
