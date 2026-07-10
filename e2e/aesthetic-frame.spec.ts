import { expect, test, type Page } from '@playwright/test'

const variants = [
  { page: 'a', id: 'carbon', light: 'rgb(243, 240, 232)', dark: 'rgb(21, 25, 26)' },
  { page: 'b', id: 'basalt', light: 'rgb(238, 240, 236)', dark: 'rgb(17, 21, 24)' },
  { page: 'c', id: 'porcelain', light: 'rgb(244, 242, 236)', dark: 'rgb(18, 23, 25)' },
] as const

async function openAesthetic(page: Page, variant: typeof variants[number]): Promise<void> {
  await page.goto(`http://127.0.0.1:4174/ui-lab/round15-${variant.page}.html`)
  await expect(page.locator('#layout-root')).toHaveAttribute('data-ready', 'true')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-aesthetic', variant.id)
  await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'light')
  await expect(page.locator('.layout-library-button')).toBeVisible()
}

async function appState(page: Page): Promise<{
  nodes: number
  regions: number
  canvas: string
  aesthetic: string | undefined
}> {
  return page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) => {
    const win = frame.contentWindow as Window & {
      __vpaDebug?: { nodeCount(): number; diagram(): { regions: unknown[] } }
      __aestheticDemo?: { aesthetic: string }
    } | null
    return {
      nodes: win?.__vpaDebug?.nodeCount() ?? 0,
      regions: win?.__vpaDebug?.diagram().regions.length ?? 0,
      canvas: frame.contentDocument?.querySelector<HTMLCanvasElement>('#c')?.style.background ?? '',
      aesthetic: win?.__aestheticDemo?.aesthetic,
    }
  })
}

test('all aesthetic options render the identical verified diagram through the real shell', async ({ page }) => {
  const identities: { nodes: number; regions: number }[] = []
  for (const variant of variants) {
    await openAesthetic(page, variant)
    const state = await appState(page)
    expect(state).toMatchObject({ nodes: 6, regions: 6, canvas: variant.light, aesthetic: variant.id })
    identities.push({ nodes: state.nodes, regions: state.regions })

    await page.locator('.layout-library-button').click()
    await expect(page.locator('.layout-library #library')).toContainText('Unload frege.json')
  }
  expect(new Set(identities.map((value) => JSON.stringify(value))).size).toBe(1)
})

test('each visual system themes the real renderer and Compass frame together', async ({ page }) => {
  for (const variant of variants) {
    await openAesthetic(page, variant)
    await page.locator('.layout-utilities-button').click()
    await page.locator('.layout-utilities > button').first().click()
    await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'dark')
    await expect.poll(async () => (await appState(page)).canvas).toBe(variant.dark)
    await page.locator('.layout-library-button').click()
    await expect(page.locator('.layout-library')).toHaveCSS('color-scheme', 'dark')

    await page.locator('.layout-utilities > button').first().click()
    await expect(page.locator('#layout-root')).toHaveAttribute('data-theme', 'light')
    await expect.poll(async () => (await appState(page)).canvas).toBe(variant.light)
  }
})

test('selection and replay remain authoritative in every aesthetic option', async ({ page }) => {
  for (const variant of variants) {
    await openAesthetic(page, variant)
    const target = await page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) => {
      const debug = (frame.contentWindow as Window & {
        __vpaDebug?: {
          bodies(): { id: string; kind: string; x: number; y: number }[]
          view(): { scale: number; offsetX: number; offsetY: number }
        }
      } | null)?.__vpaDebug
      if (debug === undefined) throw new Error('the real app debug seam is missing')
      const body = debug.bodies().find((candidate) => candidate.kind === 'ref')
      if (body === undefined) throw new Error('the verified fixture has no reference node')
      const view = debug.view()
      return { id: body.id, x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
    })
    const frameBox = await page.locator('.layout-app').boundingBox()
    if (frameBox === null) throw new Error('the real app frame has no box')
    await page.mouse.click(frameBox.x + target.x, frameBox.y + target.y)
    await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
      (frame.contentWindow as Window & { __vpaDebug?: { interaction(): { selected: { id: string }[] } } } | null)
        ?.__vpaDebug?.interaction().selected.map((hit) => hit.id) ?? [],
    )).toContain(target.id)

    await page.locator('.layout-library-button').click()
    await expect(page.locator('.layout-library #library')).toContainText('Unload frege.json')
    await page.locator('.layout-library .vpa-lib-group > button').filter({ hasText: 'frege.json' }).click()
    await page.locator('.layout-library .vpa-lib-detail button').filter({ hasText: 'Replay' }).first().click()
    const range = page.locator('.layout-time-range')
    await expect(range).toBeEnabled()
    await range.fill('3')
    await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
      (frame.contentWindow as Window & { __vpaDebug?: { replay(): { k: number } } } | null)?.__vpaDebug?.replay().k,
    )).toBe(3)
  }
})
