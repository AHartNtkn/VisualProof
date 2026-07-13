import { expect, test, type Page } from '@playwright/test'

type Point = { readonly x: number; readonly y: number }
type Region = Point & { readonly id: string; readonly kind: string; readonly r: number }
type DebugState = {
  readonly puzzle: string
  readonly timeline: { readonly cursor: number; readonly count: number }
  readonly completed: readonly string[]
  readonly viewport: { readonly regions: readonly Region[] }
}
type CursebreakerDebug = {
  state(): DebugState
  canvasToClient(point: Point): Point
  dispose(): void
}

declare global {
  interface Window { __cursebreakerDebug?: CursebreakerDebug }
}

const openGame = async (page: Page): Promise<void> => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__cursebreakerDebug !== undefined)
}

const bounds = async (page: Page, selector: string) => {
  const box = await page.locator(selector).boundingBox()
  if (box === null) throw new Error(`${selector} has no bounding box`)
  return box
}

test('one-product boot', async ({ page }) => {
  await page.goto('/')
  await expect(page).toHaveTitle('Cursebreaker')
  await expect(page.locator('#cursebreaker')).toBeVisible()
  await expect(page.locator('.curse-lens-stage')).toBeVisible()
  await expect(page.locator('#seal-canvas')).toBeVisible()
  await expect(page.locator('#chrome, .vpa-compass, #library')).toHaveCount(0)
  await expect(page.getByRole('button', { name: /forward|import|export/i })).toHaveCount(0)
  await expect(page.locator('body')).not.toContainText(/open (folder|file)|import|export/i)
})

test('straight-on responsive lens', async ({ page }) => {
  for (const viewport of [{ width: 1440, height: 900 }, { width: 700, height: 820 }]) {
    await page.setViewportSize(viewport)
    await page.goto('/')
    await expect(page.locator('.curse-lens-stage')).toBeVisible()
    const stage = await bounds(page, '.curse-lens-stage')
    const glass = await bounds(page, '.curse-lens-glass')
    const lever = await bounds(page, '.curse-timeline')
    expect(Math.abs(stage.width - stage.height)).toBeLessThanOrEqual(1)
    expect(stage.x).toBeGreaterThanOrEqual(15)
    expect(stage.y).toBeGreaterThanOrEqual(15)
    expect(viewport.width - stage.x - stage.width).toBeGreaterThanOrEqual(15)
    expect(viewport.height - stage.y - stage.height).toBeGreaterThanOrEqual(15)
    expect(Math.abs(glass.x + glass.width / 2 - (stage.x + stage.width / 2))).toBeLessThanOrEqual(1)
    expect(Math.abs(glass.y + glass.height / 2 - (stage.y + stage.height / 2))).toBeLessThanOrEqual(1)
    expect(lever.width).toBeLessThanOrEqual(stage.width * 0.4)
  }
})

test('decorative layers never own interaction', async ({ page }) => {
  await page.goto('/')
  await expect(page.locator('.curse-decoration').first()).toBeVisible()
  const decorations = await page.locator('.curse-decoration').evaluateAll((elements) => elements.map((element) => ({
    pointerEvents: getComputedStyle(element).pointerEvents,
    tabindex: element.getAttribute('tabindex'),
    alt: element instanceof HTMLImageElement ? element.alt : null,
    role: element.getAttribute('role'),
  })))
  expect(decorations.length).toBeGreaterThan(0)
  for (const decoration of decorations) {
    expect(decoration.pointerEvents).toBe('none')
    expect(decoration.tabindex).toBeNull()
    if (decoration.alt !== null) expect(decoration.alt).toBe('')
    expect(decoration.role).toBeNull()
  }
  const centerOwner = await page.locator('.curse-lens-glass').evaluate((glass) => {
    const rect = glass.getBoundingClientRect()
    return document.elementFromPoint(rect.left + rect.width / 2, rect.top + rect.height / 2)?.id
  })
  expect(centerOwner).toBe('seal-canvas')
})

test('real opening content', async ({ page }) => {
  await openGame(page)
  const keys = await page.evaluate(() => Object.keys(window.__cursebreakerDebug!).sort())
  expect(keys).toEqual(['canvasToClient', 'dispose', 'state'])
  const state = await page.evaluate(() => window.__cursebreakerDebug!.state())
  expect(state.puzzle).toBe('two-veils')
  expect(state.viewport.regions.filter((region) => region.kind === 'cut')).toHaveLength(2)
  expect(JSON.stringify(state)).not.toMatch(/theorem|library/i)
  const paletteSize = await page.locator('#seal-canvas').evaluate((canvas: HTMLCanvasElement) => {
    const context = canvas.getContext('2d')!
    const pixels = context.getImageData(0, 0, canvas.width, canvas.height).data
    const colors = new Set<string>()
    for (let index = 0; index < pixels.length; index += 4 * 97) {
      colors.add(`${pixels[index]},${pixels[index + 1]},${pixels[index + 2]},${pixels[index + 3]}`)
      if (colors.size > 1) break
    }
    return colors.size
  })
  expect(paletteSize).toBeGreaterThan(1)
})

test('backward completion retains navigable history', async ({ page }) => {
  await openGame(page)
  const outerPoint = await page.evaluate(() => {
    const debug = window.__cursebreakerDebug!
    const cuts = debug.state().viewport.regions.filter((region) => region.kind === 'cut')
      .sort((left, right) => right.r - left.r)
    const [outer, inner] = cuts
    if (outer === undefined || inner === undefined) throw new Error('opening seal has no double cut')
    const candidates = Array.from({ length: 48 }, (_, index) => {
      const angle = index * Math.PI * 2 / 48
      const point = { x: outer.x + Math.cos(angle) * outer.r * 0.88, y: outer.y + Math.sin(angle) * outer.r * 0.88 }
      return { point, clearance: Math.hypot(point.x - inner.x, point.y - inner.y) - inner.r }
    })
    const candidate = candidates.sort((left, right) => right.clearance - left.clearance)[0]!
    if (candidate.clearance <= 0) throw new Error('no exposed point on outer cut')
    return debug.canvasToClient(candidate.point)
  })
  await page.mouse.click(outerPoint.x, outerPoint.y)
  await page.mouse.click(outerPoint.x, outerPoint.y, { button: 'right' })
  await page.locator('.vpa-proof-menu').getByRole('button', { name: 'Eliminate the double cut', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().timeline)).toEqual({ cursor: 1, count: 2 })
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().completed)).toContain('two-veils')

  const rail = await bounds(page, '.curse-timeline-rail')
  await page.mouse.move(rail.x + rail.width / 2, rail.y + rail.height / 2)
  await page.mouse.down()
  await page.mouse.move(rail.x, rail.y + rail.height / 2, { steps: 5 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().timeline.cursor)).toBe(0)
  await page.mouse.move(rail.x, rail.y + rail.height / 2)
  await page.mouse.down()
  await page.mouse.move(rail.x + rail.width, rail.y + rail.height / 2, { steps: 5 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().timeline.cursor)).toBe(1)
  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().timeline.cursor)).toBe(0)
  await page.keyboard.press('Control+Shift+z')
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().timeline.cursor)).toBe(1)
  await expect(page.getByRole('button', { name: /undo|redo/i })).toHaveCount(0)
})

test('all interface assets load without browser failures', async ({ page }) => {
  const failures: string[] = []
  page.on('requestfailed', (request) => failures.push(`${request.method()} ${request.url()}: ${request.failure()?.errorText}`))
  page.on('pageerror', (error) => failures.push(`page error: ${error.message}`))
  page.on('response', (response) => { if (response.status() >= 400) failures.push(`${response.status()} ${response.url()}`) })
  await page.goto('/')
  await expect(page.locator('.curse-decoration').first()).toBeVisible()
  await expect.poll(() => page.locator('.curse-decoration').evaluateAll((images) => images
    .filter((image): image is HTMLImageElement => image instanceof HTMLImageElement)
    .every((image) => image.complete && image.naturalWidth > 0))).toBe(true)
  expect(failures).toEqual([])
})
