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
  expect(await page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __libraryDemo?: { variant: string } } | null)?.__libraryDemo?.variant,
  )).toBe('ledger')
}

const variantName = {
  a: 'aperture',
  b: 'phase',
  c: 'margin',
} as const

test('the three new projections use one real app without obsolete competing chrome', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    await expect(page.locator('#layout-root')).toHaveAttribute('data-variant', variantName[variant])
    await expect(page.locator('.layout-mode')).toHaveText(/EDIT/)
    await expect(page.locator('.layout-trail')).toHaveCount(0)
    await expect(page.locator('.layout-identity')).toHaveCount(0)
    await expect(page.locator('.layout-workflow-kicker')).toHaveCount(0)
    await expect(page.locator('.layout-utilities a')).toHaveCount(0)
    await expect(page.locator('.layout-utilities > button')).toHaveCount(1)
    await expect(page.locator('.layout-utilities')).not.toContainText(/Undo|Companion/)

    await page.locator('.layout-library-button').click()
    await expect(page.locator('.layout-library')).toBeVisible()
    await expect(page.locator('.layout-surface-head small')).toHaveText('Browse verified knowledge or manage sources')
    await expect(page.locator('.layout-library #library')).toContainText('Browse')
    await expect(page.locator('.layout-library #library')).toContainText('Sources')
    await expect(page.locator('.layout-library #library > button')).toBeHidden()

    await page.locator('.layout-close').click()
    await page.locator('.layout-mode').click()
    await page.locator('.layout-lifecycle button').nth(0).click()
    await page.locator('.layout-lifecycle button').nth(1).click()
    await page.locator('.layout-lifecycle button').nth(2).click()

    await expect(page.locator('#layout-root')).toHaveAttribute('data-mode', 'prove')
    await expect(page.locator('.layout-mode')).toContainText('PROVE')
    await expect(page.locator('.layout-temporal')).toBeVisible()
  }
})

test('every Library overlays without resizing or shifting the real application', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    const before = await page.locator('.layout-app').boundingBox()
    expect(before).not.toBeNull()
    await page.locator('.layout-library-button').click()
    await page.waitForTimeout(220)
    const after = await page.locator('.layout-app').boundingBox()
    expect(after).not.toBeNull()
    expect(after).toEqual(before)
  }
})

test('Phase Compass changes emphasis by phase while keeping one mode authority', async ({ page }) => {
  await openVariant(page, 'b')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-mode', 'edit')
  await expect(page.locator('.layout-temporal')).toBeHidden()
  await expect(page.locator('.layout-phase-note')).toContainText('Construct')

  await page.locator('.layout-mode').click()
  await page.locator('.layout-lifecycle button').nth(0).click()
  await page.locator('.layout-lifecycle button').nth(1).click()
  await page.locator('.layout-lifecycle button').nth(2).click()

  await expect(page.locator('#layout-root')).toHaveAttribute('data-mode', 'prove')
  await expect(page.locator('.layout-phase-note')).toContainText('Transform')
  await expect(page.locator('.layout-temporal')).toBeVisible()
  await expect(page.frameLocator('.layout-app').locator('#companion')).toBeHidden()
})

test('Readable Margin Compass labels its persistent global controls', async ({ page }) => {
  await openVariant(page, 'c')
  await expect(page.locator('.layout-library-button')).toHaveCSS('writing-mode', 'horizontal-tb')
  await expect(page.locator('.layout-utilities-button')).toContainText('View')
  await expect(page.locator('.layout-north')).toContainText('Workspace')
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
  }))).toEqual({ canvas: 'rgb(18, 23, 25)', rootTheme: 'dark' })

  await page.locator('.layout-library-button').click()
  await expect(page.locator('.layout-library')).toHaveCSS('color-scheme', 'dark')

  await page.locator('.layout-utilities > button').first().click()
  await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'light')
})

test('the Compass replay timeline scrubs the real replay cursor', async ({ page }) => {
  await openVariant(page, 'a')
  await page.locator('.layout-library-button').click()
  await page.locator('.lib-item-row[data-item-name="plusAssoc"]').click()
  await page.locator('.lib-replay').click()

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
