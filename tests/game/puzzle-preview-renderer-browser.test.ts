import { chromium, type Browser } from '@playwright/test'
import { createServer, type ViteDevServer } from 'vite'
import { afterAll, beforeAll, describe, expect, it } from 'vitest'

let server: ViteDevServer
let browser: Browser
let fixtureUrl: string

beforeAll(async () => {
  server = await createServer({
    root: process.cwd(),
    logLevel: 'silent',
    server: { host: '127.0.0.1', port: 0, strictPort: false },
  })
  await server.listen()
  const address = server.httpServer?.address()
  if (address === null || address === undefined || typeof address === 'string') {
    throw new Error('Vite did not expose the puzzle preview fixture')
  }
  fixtureUrl = `http://127.0.0.1:${address.port}/tests/game/puzzle-preview-renderer-fixture.html`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

describe('puzzle preview worker renderer', () => {
  it('renders a complete fixed-size Dark Slate PNG without the proof frame', async () => {
    const page = await browser.newPage()
    try {
      await page.goto(fixtureUrl)
      await page.waitForFunction(() => window.__puzzlePreviewRendererFixture?.ready === true)
      const result = await page.evaluate(() => window.__puzzlePreviewRendererFixture.valid())
      expect(result.kind).toBe('ready')
      if (!('inspection' in result)) throw new Error('preview failed')
      expect(result.inspection.width).toBe(640)
      expect(result.inspection.height).toBe(400)
      expect(result.inspection.background[3]).toBe(255)
      expect(result.inspection.bounds.minX).toBeGreaterThan(0)
      expect(result.inspection.bounds.minY).toBeGreaterThan(0)
      expect(result.inspection.bounds.maxX).toBeLessThan(639)
      expect(result.inspection.bounds.maxY).toBeLessThan(399)
    } finally {
      await page.close()
    }
  })

  it('fits a large puzzle completely inside the fixed preview', async () => {
    const page = await browser.newPage()
    try {
      await page.goto(fixtureUrl)
      await page.waitForFunction(() => window.__puzzlePreviewRendererFixture?.ready === true)
      const result = await page.evaluate(() => window.__puzzlePreviewRendererFixture.large())
      expect(result.kind).toBe('ready')
      if (!('inspection' in result)) throw new Error('large preview failed')
      expect(result.inspection.bounds.minX).toBeGreaterThan(0)
      expect(result.inspection.bounds.minY).toBeGreaterThan(0)
      expect(result.inspection.bounds.maxX).toBeLessThan(639)
      expect(result.inspection.bounds.maxY).toBeLessThan(399)
    } finally {
      await page.close()
    }
  })

  it('is deterministic and reports malformed diagrams', async () => {
    const page = await browser.newPage()
    try {
      await page.goto(fixtureUrl)
      await page.waitForFunction(() => window.__puzzlePreviewRendererFixture?.ready === true)
      expect(await page.evaluate(() => window.__puzzlePreviewRendererFixture.deterministic())).toBe(true)
      expect(await page.evaluate(() => window.__puzzlePreviewRendererFixture.malformed()))
        .toMatchObject({ kind: 'error' })
    } finally {
      await page.close()
    }
  })
})
