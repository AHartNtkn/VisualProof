import { expect, test } from './zero-signature-fixture'

test('generate a random problem and start a backward proof on it', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.getByRole('button', { name: /Mode: Edit/u }).click()
  const randomButton = page.getByRole('button', { name: 'Random…', exact: true })
  await randomButton.click()

  const dialog = page.getByRole('dialog')
  await expect(dialog).toBeVisible()
  // Small knobs so generation + search finish fast and deterministically enough.
  await dialog.getByLabel('Atoms').fill('1')
  await dialog.getByLabel('Sample connectives').fill('6')
  await dialog.getByLabel('Minimum core connectives').fill('2')
  await dialog.getByRole('button', { name: 'Generate', exact: true }).click()
  await expect(dialog).toContainText('∀')
  await expect(dialog).toContainText(/minimal proof:|no proof within/u)

  await dialog.getByRole('button', { name: 'Create diagram', exact: true }).click()
  await expect(dialog).toBeHidden()
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBeGreaterThan(0)

  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  await expect(page.locator('#status')).toContainText('PROVE')
})
