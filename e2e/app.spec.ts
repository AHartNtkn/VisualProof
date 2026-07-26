import { expect, test } from './zero-signature-fixture'

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
      dispose(): void
    }
  }
}

test('the app boots empty and loads and unloads a zero-signature theory file', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await expect(page.locator('#c')).toBeVisible()
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const library = page.locator('#library')
  await expect(library.getByRole('button', { name: 'Open folder…', exact: true })).toBeVisible()
  await expect(library.getByRole('button', { name: 'Open file…', exact: true })).toBeVisible()
  await expect(library).toContainText('No workspace folder open')
  await expect(page.getByRole('button', { name: /Mode: Edit/ })).toBeVisible()
  await expect(page.locator('#status')).toContainText('EDIT')

  expect(await page.evaluate(() => ({
    nodes: window.__vpaDebug!.nodeCount(),
    status: window.__vpaDebug!.status(),
    interaction: window.__vpaDebug!.interaction(),
  }))).toEqual({
    nodes: 0,
    status: expect.stringContaining('EDIT'),
    interaction: { selected: [], pins: [], userZoom: 1 },
  })

  await page.locator('#open-file-input').setInputFiles(theoryFiles.tiny)
  await expect(library.getByRole('button', {
    name: 'Unload zero-signature.json',
    exact: true,
  })).toBeVisible()
  await library.getByRole('button', { name: '▸ zero-signature.json', exact: true }).click()
  await expect(library).toContainText('StructuralReflexivity')
  await expect(library).toContainText('UnaryWitness')

  await library.getByRole('button', {
    name: 'Unload zero-signature.json',
    exact: true,
  }).click()
  await expect(library).not.toContainText('StructuralReflexivity')
  await expect(page.locator('#status')).toContainText('EDIT')
})

test('the keyboard map exposes the surviving structural shortcuts', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const map = page.locator('.vpa-keyboard-map')
  await expect(map).toBeHidden()
  await page.getByRole('button', { name: 'Utilities', exact: true }).click()
  await page.getByRole('button', { name: 'Keyboard map', exact: true }).click()
  await expect(map).toBeVisible()
  await expect(map).toContainText('Ctrl+Z undo')
  await expect(map).toContainText('Home fit')
  await expect(map).toContainText('Delete contextual erase')
})

test('an invalid theory file reports a visible library error', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.locator('#open-file-input').setInputFiles(theoryFiles.invalid)

  await expect(page.locator('#library')).toContainText('load failed:')
  await expect(page.locator('#library')).toContainText('Unexpected end of JSON input')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(0)
})
