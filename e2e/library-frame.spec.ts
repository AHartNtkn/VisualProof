import { expect, test, type Page } from '@playwright/test'

type Variant = 'a' | 'b' | 'c'

async function openVariant(page: Page, variant: Variant): Promise<void> {
  await page.goto(`http://127.0.0.1:4174/ui-lab/round16-${variant}.html`)
  await expect(page.locator('#layout-root')).toHaveAttribute('data-ready', 'true')
  await expect(page.locator('.layout-library')).toBeVisible()
  await expect(page.locator('.lib-result-count')).toHaveText('16 of 16 verified items')
}

async function openSources(page: Page, variant: Variant): Promise<void> {
  if (variant === 'a') await page.locator('.lib-mode-tabs button').filter({ hasText: 'Sources' }).click()
  else if (variant === 'b') await page.locator('.lib-projection-route').click()
  else await page.locator('.lib-manage').click()
  await expect(page.locator('.lib-source-list')).toBeVisible()
}

async function openKnowledge(page: Page, variant: Variant): Promise<void> {
  if (variant === 'a') await page.locator('.lib-mode-tabs button').filter({ hasText: 'Browse' }).click()
  else await page.locator('.lib-projection-route').click()
  await expect(page.locator('.lib-results')).toBeVisible()
}

function sourceRow(page: Page, file: string) {
  return page.locator(`.lib-source-row[data-source-file="${file}"]`)
}

test('all projections are views of the same flat verified-knowledge catalogue', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    await expect(page.locator('.lib-item-row[data-item-name="sessionIdentity"]')).toContainText('Session')
    await expect(page.locator('.lib-item-row[data-item-name="sessionZero"]')).toContainText('Session')

    await page.locator('.lib-search').fill('session')
    await expect(page.locator('.lib-result-count')).toHaveText('2 of 16 verified items')
    await expect(page.locator('.lib-item-row')).toHaveCount(2)

    await page.locator('.lib-filters button').filter({ hasText: 'Relations' }).click()
    await expect(page.locator('.lib-item-row')).toHaveCount(1)
    await expect(page.locator('.lib-item-row')).toHaveAttribute('data-item-name', 'sessionZero')
  }
})

test('source management uses the authoritative load lifecycle and local diagnostics', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    await openSources(page, variant)

    await expect(sourceRow(page, 'frege.json')).toContainText('Loaded')
    await expect(sourceRow(page, 'lambda.json')).toContainText('Loaded')
    await expect(sourceRow(page, 'available.json')).toContainText('Available')
    await expect(sourceRow(page, 'broken.json')).toContainText('Load failed')
    await expect(sourceRow(page, 'broken.json').locator('.lib-source-error')).toBeVisible()
    await expect(sourceRow(page, 'Session')).toContainText('Live')

    await sourceRow(page, 'available.json').locator('.lib-source-action').click()
    await expect(sourceRow(page, 'available.json')).toContainText('Loaded')
    await openKnowledge(page, variant)
    await expect(page.locator('.lib-result-count')).toHaveText('17 of 17 verified items')
    await expect(page.locator('.lib-item-row[data-item-name="availableZero"]')).toContainText('available.json')
  }
})

test('relation and theorem drill-ins use real diagrams and theorem replay', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)

    await page.locator('.lib-item-row[data-item-kind="relation"]').first().click()
    await expect(page.locator('.lib-inspector-heading')).toContainText('REL')
    await expect(page.locator('.lib-preview')).toHaveCount(1)
    await expect(page.locator('.lib-prototype button')).not.toContainText('Spawn')
    await page.locator('.lib-back').click()

    await page.locator('.lib-item-row[data-item-name="plusAssoc"]').click()
    await expect(page.locator('.lib-inspector-heading')).toContainText('THM')
    await expect(page.locator('.lib-preview')).toHaveCount(2)
    await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
      frame.contentDocument?.body === undefined || frame.contentDocument.body === null || frame.contentWindow === null
        ? ''
        : frame.contentWindow.getComputedStyle(frame.contentDocument.body).backgroundColor,
    )).toBe('rgb(244, 242, 236)')
    await page.locator('.lib-replay').click()

    await expect(page.locator('.layout-library')).toBeHidden()
    const range = page.locator('.layout-time-range')
    await expect(range).toBeEnabled()
    const last = Number(await range.getAttribute('max'))
    expect(last).toBeGreaterThan(2)
    await range.fill('3')
    await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
      (frame.contentWindow as Window & { __vpaDebug?: { replay(): { k: number } } } | null)?.__vpaDebug?.replay().k,
    )).toBe(3)
  }
})

test('keyboard search, inspector escape, and drawer escape form one focus-safe path', async ({ page }) => {
  await openVariant(page, 'a')
  const first = page.locator('.lib-item-row').first()
  await first.focus()
  await page.keyboard.press('/')
  await expect(page.locator('.lib-search')).toBeFocused()
  await page.locator('.lib-search').fill('plusAssoc')
  await page.locator('.lib-item-row').click()
  await expect(page.locator('.lib-inspector-heading')).toContainText('plusAssoc')

  await page.keyboard.press('Escape')
  await expect(page.locator('.lib-results')).toBeVisible()
  await page.keyboard.press('Escape')
  await expect(page.locator('.lib-search')).toHaveValue('')
  await page.keyboard.press('Escape')
  await expect(page.locator('.layout-library')).toBeHidden()
  await expect(page.locator('.layout-library-button')).toBeFocused()
})

test('the Source Shelf keeps its management route visible at drawer width', async ({ page }) => {
  await openVariant(page, 'c')
  const shelf = await page.locator('.lib-source-shelf').boundingBox()
  const manage = await page.locator('.lib-manage').boundingBox()
  expect(shelf).not.toBeNull()
  expect(manage).not.toBeNull()
  expect(manage!.x + manage!.width).toBeLessThanOrEqual(shelf!.x + shelf!.width + 1)
  await expect(page.locator('.lib-manage')).toBeVisible()
})
