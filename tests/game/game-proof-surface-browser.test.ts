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
  const page = await browser.newPage({ viewport: { width: 960, height: 720 } })
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
      expect(result.mapping.screen).toEqual({ x: 240, y: 180 })
    } finally { await page.close() }
  })

  it('opens the one game loupe, blocks proof shortcuts beneath it, and gives Escape to editor close', async () => {
    const page = await openFixture()
    try {
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.open())).toBe(true)
      await page.waitForSelector('.cursebreaker-construction-loupe')
      const before = await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())
      await page.keyboard.press('F')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())).toBe(before)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.editing())).toBe(true)
      await page.keyboard.press('Escape')
      await page.waitForSelector('.cursebreaker-construction-loupe', { state: 'detached' })
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.editing())).toBe(false)
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
})
