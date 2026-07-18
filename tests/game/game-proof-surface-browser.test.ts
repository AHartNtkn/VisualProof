import { chromium, type Browser, type Page } from '@playwright/test'
import { createServer, type ViteDevServer } from 'vite'
import { afterAll, beforeAll, describe, expect, it } from 'vitest'

let server: ViteDevServer
let browser: Browser
let fixtureUrl: string

beforeAll(async () => {
  server = await createServer({
    root: process.cwd(),
    logLevel: 'silent',
    server: {
      host: '127.0.0.1', port: 0, strictPort: false,
      watch: { ignored: ['**/.tools/**', '**/node_modules/**', '**/.git/**'] },
    },
  })
  await server.listen()
  const address = server.httpServer?.address()
  if (address === null || address === undefined || typeof address === 'string') {
    throw new Error('Vite did not expose a game proof surface fixture address')
  }
  fixtureUrl = `http://127.0.0.1:${address.port}/tests/game/game-proof-surface-fixture.html`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

const openFixture = async (): Promise<Page> => {
  const page = await browser.newPage({ viewport: { width: 1600, height: 720 } })
  await page.goto(fixtureUrl)
  await page.waitForSelector('.curse-game-proof-canvas')
  return page
}

describe('rendered game proof surface', () => {
  it('keeps the substrate-visible canvas transparent and maps live geometry exactly', async () => {
    const page = await openFixture()
    try {
      const result = await page.evaluate(() => ({
        alpha: window.__gameProofSurfaceFixture.cornerAlpha(),
        mapping: window.__gameProofSurfaceFixture.mapping({ x: 240, y: 180 }),
        background: getComputedStyle(document.querySelector('.curse-game-proof-canvas')!).backgroundColor,
      }))
      expect(result.alpha).toBe(0)
      expect(result.background).toBe('rgba(0, 0, 0, 0)')
      const canvas = await page.locator('.curse-game-proof-canvas').boundingBox()
      if (canvas === null) throw new Error('proof canvas missing')
      const backingWidth = await page.locator('.curse-game-proof-canvas').evaluate((node) => (node as HTMLCanvasElement).width)
      expect(result.mapping.screen.x).toBeCloseTo((240 - canvas.x) * backingWidth / canvas.width, 5)
      const point = await page.evaluate(() => window.__gameProofSurfaceFixture.proofNodePoint())
      await page.mouse.click(point.x, point.y)
      expect((await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).length).toBe(1)
    } finally { await page.close() }
  })

  it('opens the one game loupe, blocks proof shortcuts beneath it, and gives Escape to editor close', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => window.__gameProofSurfaceFixture.clearSelection())
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.open())).toBe(true)
      await page.waitForSelector('.cursebreaker-construction-loupe')
      const loupeCanvas = page.locator('.cursebreaker-construction-loupe__canvas')
      await loupeCanvas.click({ button: 'right', position: { x: 210, y: 210 } })
      await page.getByRole('button', { name: /λ term/ }).click()
      await page.locator('.vpa-spawn-search').fill('x')
      await page.keyboard.press('Enter')
      const hostPoint = await page.evaluate(() => {
        const proofCanvas = document.querySelector('.curse-game-proof-canvas')
        return window.__gameProofSurfaceFixture.construction()!.hostWires.find((wire) => wire.point !== null
          && document.elementFromPoint(wire.point.x, wire.point.y) === proofCanvas)?.point ?? null
      })
      if (hostPoint === null) throw new Error('no host line is pointer reachable')
      await page.mouse.click(hostPoint.x, hostPoint.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])
      await page.mouse.move(hostPoint.x, hostPoint.y)
      await page.mouse.down()
      const draftPoint = await page.evaluate(() => {
        const debug = window.__gameProofSurfaceFixture.construction()!
        const target = debug.connection!.draftTargets[0]!
        return debug.draftWires.find((wire) => wire.wire === target)!.point!
      })
      await page.mouse.move(draftPoint.x, draftPoint.y)
      await page.mouse.up()
      expect((await page.evaluate(() => window.__gameProofSurfaceFixture.construction()!.externalWires)).length).toBe(1)
      const before = await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())
      await page.keyboard.press('F')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())).toBe(before)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.editing())).toBe(true)
      await page.keyboard.press('Escape')
      await page.waitForSelector('.cursebreaker-construction-loupe', { state: 'detached' })
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.editing())).toBe(false)
    } finally { await page.close() }
  })

  it('keeps rendered timeline centers, pointer mapping, ARIA, and keyboard focus aligned', async () => {
    const page = await openFixture()
    try {
      const slider = page.locator('.curse-production-timeline-control')
      const renderedCenters: number[] = []
      for (const cursor of [0, 3, 7]) {
        await page.evaluate((value) => window.__gameProofSurfaceFixture.setTimelineCursor(value), cursor)
        const center = await page.locator('.curse-production-timeline-handle').evaluate((node) => {
          const rect = node.getBoundingClientRect()
          return { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
        })
        renderedCenters.push(center.x)
        await page.mouse.click(center.x, center.y)
        expect((await page.evaluate(() => window.__gameProofSurfaceFixture.timeline())).requests.at(-1)).toBe(cursor)
      }
      await page.evaluate(() => window.__gameProofSurfaceFixture.selectParameter())
      const prepared = await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())
      const changed = await page.evaluate(() => window.__gameProofSurfaceFixture.changed())
      await slider.focus()
      await page.keyboard.press('Home')
      await page.keyboard.press('ArrowRight')
      await page.keyboard.press('F')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.timeline().cursor)).toBe(1)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())).toBe(prepared)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.changed())).toBe(changed)
      expect(await slider.getAttribute('aria-valuenow')).toBe('1')
      await page.locator('.curse-game-proof-canvas').focus()
      await page.keyboard.press('Home')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.changed())).toBe(changed + 1)
      const control = await slider.boundingBox()
      const handle = await page.locator('.curse-production-timeline-handle').boundingBox()
      if (control === null || handle === null) throw new Error('timeline geometry missing')
      expect(handle.x + handle.width / 2).toBeCloseTo(renderedCenters[0]! + (renderedCenters[2]! - renderedCenters[0]!) / 7, 1)
    } finally { await page.close() }
  })

  it('routes a refused live artifact drop to pointer feedback without preparing a state change', async () => {
    const page = await openFixture()
    try {
      const before = await page.evaluate(() => ({
        prepared: window.__gameProofSurfaceFixture.prepared(),
        refusals: window.__gameProofSurfaceFixture.refusals(),
      }))
      await page.evaluate(() => window.__gameProofSurfaceFixture.refuseIncompleteArtifact())
      expect(await page.evaluate(() => ({
        prepared: window.__gameProofSurfaceFixture.prepared(),
        refusals: window.__gameProofSurfaceFixture.refusals(),
      }))).toEqual({ prepared: before.prepared, refusals: before.refusals + 1 })
    } finally { await page.close() }
  })

  it('makes construction and artifact entry inert after proof-surface disposal', async () => {
    const page = await openFixture()
    try {
      const result = await page.evaluate(() => window.__gameProofSurfaceFixture.disposeAndProbe())
      expect(result.opened).toBe(false)
      expect(result.drop.ok).toBe(false)
      expect(result.after).toEqual(result.before)
      expect(await page.locator('.cursebreaker-construction-loupe').count()).toBe(0)
    } finally { await page.close() }
  })
})
