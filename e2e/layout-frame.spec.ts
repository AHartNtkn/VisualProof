import { expect, test, type Page } from '@playwright/test'

const demo = (variant: 'a' | 'b' | 'c'): string =>
  `http://127.0.0.1:4174/ui-lab/round14-${variant}.html`

async function openVariant(page: Page, variant: 'a' | 'b' | 'c'): Promise<void> {
  await page.goto(demo(variant))
  await expect(page.locator('#layout-root')).toHaveAttribute('data-ready', 'true')
  await expect(page.locator('.layout-app')).toBeVisible()
  expect(await page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    typeof (frame.contentWindow as Window & { __vpaDebug?: unknown } | null)?.__vpaDebug,
  )).toBe('object')
}

test('every layout uses the real shell library and follows its authoritative mode', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)

    await page.locator('.layout-library-button').click()
    await expect(page.locator('.layout-library')).toBeVisible()
    await expect(page.locator('.layout-library #library')).toContainText('No workspace folder open')
    await expect(page.locator('.layout-library #library > button')).toBeHidden()

    const app = page.frameLocator('.layout-app')
    await app.locator('#open-file-input').setInputFiles('examples/frege.json')
    await expect(page.locator('.layout-library #library')).toContainText('Unload frege.json')

    await page.locator('.layout-close').click()
    await page.locator(variant === 'b' ? '.layout-trail-step:nth-child(2)' : '.layout-mode').click()
    await page.locator('.layout-lifecycle button').nth(0).click()
    await page.locator('.layout-lifecycle button').nth(1).click()
    await page.locator('.layout-lifecycle button').nth(2).click()

    await expect(page.locator(variant === 'b' ? '.layout-trail-step:nth-child(2)' : '.layout-mode')).toContainText('PROVE')
    await expect(page.locator('.layout-temporal')).toBeVisible()
  }
})

test('only the Workbench library bay resizes the real application viewport', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    const before = await page.locator('.layout-app').boundingBox()
    expect(before).not.toBeNull()
    await page.locator('.layout-library-button').click()
    await page.waitForTimeout(220)
    const after = await page.locator('.layout-app').boundingBox()
    expect(after).not.toBeNull()
    if (variant === 'c') {
      expect(after!.x).toBeGreaterThan(before!.x + 250)
      expect(after!.width).toBeLessThan(before!.width - 250)
    } else {
      expect(after).toEqual(before)
    }
  }
})

test('all three frames remain operable at a constrained desktop width', async ({ page }) => {
  await page.setViewportSize({ width: 680, height: 720 })
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    await page.locator('.layout-library-button').click()
    const library = await page.locator('.layout-library').boundingBox()
    const viewport = page.viewportSize()
    expect(library).not.toBeNull()
    expect(viewport).not.toBeNull()
    expect(library!.x).toBeGreaterThanOrEqual(0)
    expect(library!.x + library!.width).toBeLessThanOrEqual(viewport!.width)
  }
})

test('the Compass frame and real app share one theme state', async ({ page }) => {
  await openVariant(page, 'a')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'light')

  await page.locator('.layout-utilities-button').click()
  await page.locator('.layout-utilities > button').first().click()
  await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'dark')
  expect(await page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) => ({
    canvas: frame.contentDocument?.querySelector<HTMLCanvasElement>('#c')?.style.background,
    rootTheme: frame.contentDocument?.documentElement.dataset.layoutTheme,
  }))).toEqual({ canvas: 'rgb(14, 16, 19)', rootTheme: 'dark' })

  await page.locator('.layout-library-button').click()
  await expect(page.locator('.layout-library')).toHaveCSS('color-scheme', 'dark')

  await page.locator('.layout-utilities > button').first().click()
  await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'light')
})

test('the Compass replay timeline scrubs the real replay cursor', async ({ page }) => {
  await openVariant(page, 'a')
  await page.locator('.layout-library-button').click()
  await page.frameLocator('.layout-app').locator('#open-file-input').setInputFiles('examples/frege.json')
  await page.locator('.layout-library .vpa-lib-group > button').filter({ hasText: 'frege.json' }).click()
  await page.locator('.layout-library .vpa-lib-detail button').filter({ hasText: 'Replay' }).first().click()

  const range = page.locator('.layout-time-range')
  await expect(page.locator('.layout-temporal')).toBeVisible()
  await expect(range).toBeEnabled()
  const last = Number(await range.getAttribute('max'))
  expect(last).toBeGreaterThan(2)

  await range.fill('3')
  await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __vpaDebug?: { replay(): { k: number } } } | null)?.__vpaDebug?.replay().k,
  )).toBe(3)
  await expect(range).toHaveValue('3')

  await page.locator('.layout-undo').click()
  await expect(range).toHaveValue('2')
})
