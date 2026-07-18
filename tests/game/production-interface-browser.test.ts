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
    server: { host: '127.0.0.1', port: 0, strictPort: false },
  })
  await server.listen()
  const address = server.httpServer?.address()
  if (address === null || address === undefined || typeof address === 'string') {
    throw new Error('Vite did not expose a production-interface fixture address')
  }
  fixtureUrl = `http://127.0.0.1:${address.port}/tests/game/production-interface-fixture.html`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

const openFixture = async (viewport: { width: number; height: number }): Promise<Page> => {
  const page = await browser.newPage({ viewport })
  await page.goto(fixtureUrl)
  await page.waitForSelector('.curse-production-environment')
  return page
}

describe('production interface rendered geometry', () => {
  it('preserves a usable compact drawer edge', async () => {
    const page = await openFixture({ width: 760, height: 900 })
    try {
      const initial = await page.evaluate(() => {
        const host = document.querySelector<HTMLElement>('.curse-production-folio-host')!
        const folio = host.querySelector<HTMLElement>('.curse-folio')!
        const hostRect = host.getBoundingClientRect()
        const folioRect = folio.getBoundingClientRect()
        return {
          hostRight: hostRect.right,
          visibleFolioEdge: Math.max(0, Math.min(innerWidth, folioRect.right)),
        }
      })
      expect(initial.hostRight).toBeCloseTo(52, 0)
      expect(initial.visibleFolioEdge).toBeGreaterThanOrEqual(44)
    } finally {
      await page.close()
    }
  })

  it('makes deterministic substrate crop coordinates change rendered sampling geometry', async () => {
    const page = await openFixture({ width: 760, height: 900 })
    try {
      const initialCenter = await page.locator('.curse-production-substrate').evaluate((node) => {
        const rect = node.getBoundingClientRect()
        return { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
      })
      await page.evaluate(() => window.__productionInterfaceFixture.setSeed('second:0002'))
      const changedCenter = await page.locator('.curse-production-substrate').evaluate((node) => {
        const rect = node.getBoundingClientRect()
        return { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
      })
      expect(Math.hypot(
        changedCenter.x - initialCenter.x,
        changedCenter.y - initialCenter.y,
      )).toBeGreaterThan(1)
    } finally {
      await page.close()
    }
  })

  it('anchors actual production-folio records to client coordinates in desktop and compact styling', async () => {
    const page = await openFixture({ width: 1400, height: 900 })
    try {
      const source = page.locator(
        '.curse-production-folio-host [data-puzzle="browser-completed-record"]',
      )
      const sourceBox = await source.boundingBox()
      if (sourceBox === null) throw new Error('completed drag record has no rendered box')
      await page.mouse.move(sourceBox.x + sourceBox.width / 2, sourceBox.y + sourceBox.height / 2)
      await page.mouse.down()
      await page.mouse.move(980, 350)
      const lifted = await source.boundingBox()
      if (lifted === null) throw new Error('lifted record has no rendered box')
      expect(lifted.x + lifted.width / 2).toBeCloseTo(980, 0)
      expect(lifted.y + lifted.height / 2).toBeCloseTo(350, 0)

      await page.evaluate(() => window.__productionInterfaceFixture.replaceDragView())
      expect(await page.evaluate(() => window.__productionInterfaceFixture.dragCleanup())).toEqual({
        cancellations: 1,
        connected: false,
        lifted: false,
        x: '',
        y: '',
        captured: false,
      })
      await page.mouse.up()

      await page.setViewportSize({ width: 760, height: 900 })
      await page.evaluate(() => {
        const fixture = window.__productionInterfaceFixture
        fixture.setLayout(innerWidth, innerHeight)
        fixture.setFolioLeft(100)
      })
      const replacement = page.locator(
        '.curse-production-folio-host [data-puzzle="browser-completed-record"]',
      )
      const replacementBox = await replacement.boundingBox()
      if (replacementBox === null) throw new Error('replacement drag record has no rendered box')
      await page.mouse.move(
        replacementBox.x + replacementBox.width / 2,
        replacementBox.y + replacementBox.height / 2,
      )
      await page.mouse.down()
      await page.mouse.move(900, 420)
      const compactOffsetLifted = await replacement.boundingBox()
      if (compactOffsetLifted === null) throw new Error('compact-offset lift has no rendered box')
      expect(compactOffsetLifted.x + compactOffsetLifted.width / 2).toBeCloseTo(900, 0)
      expect(compactOffsetLifted.y + compactOffsetLifted.height / 2).toBeCloseTo(420, 0)
      await page.evaluate(() => window.__productionInterfaceFixture.disposeDragView())
      expect(await page.evaluate(() => window.__productionInterfaceFixture.dragCleanup())).toEqual({
        cancellations: 2,
        connected: false,
        lifted: false,
        x: '',
        y: '',
        captured: false,
      })
      await page.mouse.up()
    } finally {
      await page.close()
    }
  })
})
