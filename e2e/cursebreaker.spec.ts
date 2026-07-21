import { expect, test, type Page } from '@playwright/test'

type Point = { readonly x: number; readonly y: number }
type Region = {
  readonly id: string
  readonly kind: string
  readonly client: Point
  readonly interiorClient: Point
  readonly rimClient: Point
}
type DebugState = {
  readonly state: {
    readonly mode: 'archive' | 'puzzle' | 'completion'
    readonly activePuzzle: string | null
    readonly completedArtifacts: ReadonlyMap<string, unknown>
    readonly completionReceipt: { readonly puzzle: string; readonly moves: number; readonly replay: boolean } | null
  }
  readonly timeline: { readonly cursor: number; readonly count: number } | null
  readonly proofRegions: readonly Region[]
}
type CursebreakerDebug = {
  state(): DebugState
  dispatch(action: { readonly kind: string; readonly puzzle?: string; readonly cursor?: number }): void
  settled(): Promise<void>
  canvasToClient(point: Point): Point
  dispose(): void
}

declare global {
  interface Window { __cursebreakerDebug?: CursebreakerDebug }
}

test.beforeEach(async ({ page }) => {
  await page.addInitScript(() => {
    let save: unknown | null = null
    Object.defineProperty(window, 'cursebreakerPlatform', {
      value: {
        async loadSave() { return save },
        async writeSave(document: unknown) { save = document },
        async replaceInvalidSave(document: unknown) { save = document },
        async rendererReady() {},
        async reportStartupFailure(message: string) { throw new Error(message) },
        async setFullscreen(fullscreen: boolean) { return fullscreen },
        async requestExit(document: unknown) { save = document },
        onExitRequested(_callback: () => void) { return () => {} },
      },
    })
  })
})

const openGame = async (page: Page): Promise<void> => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__cursebreakerDebug !== undefined)
}

const openFirstPuzzle = async (page: Page): Promise<void> => {
  await openGame(page)
  const record = page.locator('[data-puzzle="two-veils"]')
  await expect(record.locator('.curse-folio-puzzle-preview-frame[data-preview-state="ready"]'))
    .toBeVisible()
  await record.click()
  await expect(page.locator('.curse-game-proof-canvas')).toBeVisible()
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
  await expect(page.locator('.curse-production-lens')).toBeVisible()
  await expect(page.locator('[data-puzzle="two-veils"]')).toBeVisible()
  await expect(page.locator('[data-puzzle="two-veils"] .curse-folio-puzzle-preview-frame[data-preview-state="ready"]'))
    .toBeVisible()
  await page.locator('[data-puzzle="two-veils"]').hover()
  await expect(page.locator('.curse-folio-puzzle-preview-inspection')).toHaveCount(0)
  await expect(page.locator('.curse-game-proof-canvas')).toHaveCount(0)
  await page.locator('[data-puzzle="two-veils"]').click()
  await expect(page.locator('.curse-game-proof-canvas')).toBeVisible()
  await expect(page.locator('#chrome, .vpa-compass, #library')).toHaveCount(0)
  await expect(page.getByRole('button', { name: /^(forward|import|export)$/i })).toHaveCount(0)
  await expect(page.locator('body')).not.toContainText(/open (folder|file)|import|export/i)
})

test('straight-on responsive lens', async ({ page }) => {
  for (const viewport of [{ width: 1440, height: 900 }, { width: 700, height: 820 }]) {
    await page.setViewportSize(viewport)
    await page.goto('/')
    await expect(page.locator('.curse-production-lens')).toBeVisible()
    const stage = await bounds(page, '.curse-production-lens')
    const glass = await bounds(page, '.curse-production-aperture')
    const lever = await bounds(page, '.curse-production-timeline')
    expect(Math.abs(stage.width - stage.height)).toBeLessThanOrEqual(1)
    expect(stage.x).toBeGreaterThanOrEqual(0)
    expect(stage.y).toBeGreaterThanOrEqual(0)
    expect(viewport.width - stage.x - stage.width).toBeGreaterThanOrEqual(0)
    expect(viewport.height - stage.y - stage.height).toBeGreaterThanOrEqual(0)
    expect(glass.x).toBeGreaterThanOrEqual(stage.x)
    expect(glass.y).toBeGreaterThanOrEqual(stage.y)
    expect(glass.x + glass.width).toBeLessThanOrEqual(stage.x + stage.width)
    expect(glass.y + glass.height).toBeLessThanOrEqual(stage.y + stage.height)
    expect(lever.x).toBeGreaterThanOrEqual(stage.x)
    expect(lever.x + lever.width).toBeLessThanOrEqual(stage.x + stage.width)
  }
})

test('decorative layers never own interaction', async ({ page }) => {
  await openFirstPuzzle(page)
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
  const centerOwner = await page.locator('.curse-production-aperture').evaluate((glass) => {
    const rect = glass.getBoundingClientRect()
    return document.elementFromPoint(rect.left + rect.width / 2, rect.top + rect.height / 2)?.classList
      .contains('curse-game-proof-canvas') ?? false
  })
  expect(centerOwner).toBe(true)
})

test('real opening content', async ({ page }) => {
  await openFirstPuzzle(page)
  const keys = await page.evaluate(() => Object.keys(window.__cursebreakerDebug!).sort())
  expect(keys).toEqual(['canvasToClient', 'dispatch', 'dispose', 'settled', 'state'])
  const state = await page.evaluate(() => window.__cursebreakerDebug!.state())
  expect(state.state.activePuzzle).toBe('two-veils')
  expect(state.proofRegions.filter((region) => region.kind === 'cut')).toHaveLength(2)
  expect(JSON.stringify(state)).not.toMatch(/theorem|library/i)
  const paletteSize = await page.locator('.curse-game-proof-canvas').evaluate((canvas: HTMLCanvasElement) => {
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

test('backward completion records the solved artifact through the live rule interaction', async ({ page }) => {
  await openFirstPuzzle(page)
  const outerPoint = await page.evaluate(() => {
    const debug = window.__cursebreakerDebug!
    const outer = debug.state().proofRegions.find((region) => region.id === 'r1')
    if (outer === undefined) throw new Error('opening seal has no outer cut')
    return outer.rimClient
  })
  await page.mouse.click(outerPoint.x, outerPoint.y)
  await page.mouse.click(outerPoint.x, outerPoint.y, { button: 'right' })
  await page.locator('.curse-proof-menu').getByRole('button', { name: 'Eliminate the double cut', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__cursebreakerDebug!.state().state.mode))
    .toBe('completion')
  expect(await page.evaluate(() => {
    const state = window.__cursebreakerDebug!.state().state
    return {
      completed: state.completedArtifacts.has('two-veils'),
      receipt: state.completionReceipt,
    }
  })).toEqual({
    completed: true,
    receipt: { puzzle: 'two-veils', moves: 1, replay: false },
  })
  await expect(page.locator('.curse-production-timeline-control')).toHaveAttribute('aria-disabled', 'true')
  await expect(page.locator('.curse-production-timeline-control')).toHaveAttribute('aria-valuetext', 'Completed state 1')
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
