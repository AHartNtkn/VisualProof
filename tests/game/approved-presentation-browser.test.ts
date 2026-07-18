import { chromium, type Browser, type Page } from '@playwright/test'
import { createServer, type ViteDevServer } from 'vite'
import { afterAll, beforeAll, describe, expect, it } from 'vitest'

let server: ViteDevServer
let browser: Browser
let rootUrl: string

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
    throw new Error('Vite did not expose an approved-presentation fixture address')
  }
  rootUrl = `http://127.0.0.1:${address.port}`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

const open = async (path: string, viewport: { width: number, height: number }): Promise<Page> => {
  const page = await browser.newPage({ viewport })
  await page.goto(`${rootUrl}${path}`)
  await page.waitForFunction(() => Array.from(
    document.querySelectorAll<HTMLImageElement>('.curse-decoration'),
  ).every((image) => image.complete && image.naturalWidth > 0))
  return page
}

describe('approved production presentation conformance', () => {
  it('renders the approved full-lens mechanics and physical dossier composition', async () => {
    const page = await open('/tests/game/approved-presentation-fixture.html', { width: 1600, height: 1000 })
    try {
      const result = await page.evaluate(() => {
        const rect = (selector: string) => {
          const node = document.querySelector<HTMLElement>(selector)
          if (node === null) throw new Error(`missing ${selector}`)
          const { x, y, width, height } = node.getBoundingClientRect()
          return { x, y, width, height }
        }
        const records = [...document.querySelectorAll<HTMLElement>('.curse-folio-record')]
          .map((node) => rect(`[data-puzzle="${node.dataset.puzzle}"]`))
        return {
          lens: rect('.curse-production-lens'),
          gasket: rect('.curse-production-gasket'),
          housing: rect('.curse-production-timeline-housing'),
          handleLayer: rect('.curse-production-timeline-handle-slot'),
          folio: rect('.curse-production-folio-host'),
          title: document.querySelector('.dossier-title')?.textContent,
          folioFont: getComputedStyle(document.querySelector('.curse-folio')!).fontFamily,
          tabs: [...document.querySelectorAll('.curse-folio-culture-label')]
            .map((node) => node.textContent),
          physicalLayers: ['.folio-board-lower', '.dossier-underlay', '.guard-leaf-layer',
            '.active-dossier', '.folio-cover', '.inspection-stage']
            .map((selector) => document.querySelectorAll(selector).length),
          records,
        }
      })
      expect(result.lens).toEqual({ x: 600, y: 0, width: 1000, height: 1000 })
      expect(result.gasket).toEqual(result.lens)
      expect(result.housing).toEqual(result.lens)
      expect(result.handleLayer).toEqual(result.lens)
      expect(result.folio.width).toBeCloseTo(628.8, 0)
      expect(result.title).toBe('Excavation archive · Seyric dossier')
      expect(result.folioFont).toContain('Georgia')
      expect(result.tabs).toEqual(['Seyric', 'Myratic'])
      expect(result.physicalLayers).toEqual([1, 2, 1, 1, 1, 1])
      expect(result.records.every(({ width, height }) => width > 0 && height > 0)).toBe(true)
    } finally { await page.close() }
  })

  it('animates every physical channel through the one production coordinator', async () => {
    const samples: Array<{
      trigger(page: Page): Promise<void>
      channel: string
      subject: string
    }> = [
      { channel: 'cover', subject: '.cover-surface', trigger: async (page) => { await page.locator('.cover-spine-hit').click() } },
      { channel: 'dossier', subject: '.active-dossier', trigger: async (page) => { await page.evaluate(() => window.__approvedPresentationFixture.dossier()) } },
      { channel: 'restriction', subject: '[data-puzzle="locked-seal"] .record-guard', trigger: async (page) => { await page.evaluate(() => window.__approvedPresentationFixture.restriction()) } },
      { channel: 'packet', subject: '[data-puzzle="restricted-packet"] .record-guard', trigger: async (page) => { await page.evaluate(() => window.__approvedPresentationFixture.packet()) } },
    ]
    for (const sample of samples) {
      const page = await open('/tests/game/approved-presentation-fixture.html', { width: 1600, height: 1000 })
      try {
        await page.evaluate(({ channel, subject }) => {
          delete document.documentElement.dataset.presentationMotionSample
          const root = document.querySelector('.curse-folio')
          if (!(root instanceof HTMLElement)) throw new Error('folio motion root missing')
          const capture = () => {
            if (!root.classList.contains(`is-motion-${channel}`)) return
            const node = document.querySelector(subject)
            if (!(node instanceof HTMLElement)) return
            const style = getComputedStyle(node)
            document.documentElement.dataset.presentationMotionSample = JSON.stringify({
              animation: style.animationName,
              transform: style.transform,
              opacity: style.opacity,
            })
          }
          const observer = new MutationObserver(() => {
            capture()
            if (document.documentElement.dataset.presentationMotionSample !== undefined) {
              observer.disconnect()
            }
          })
          observer.observe(root, { attributes: true })
          capture()
        }, { channel: sample.channel, subject: sample.subject })
        await sample.trigger(page)
        await page.waitForFunction(() => document.documentElement
          .dataset.presentationMotionSample !== undefined)
        const active = await page.evaluate(() => JSON.parse(document.documentElement
          .dataset.presentationMotionSample!)) as {
            animation: string
            transform: string
            opacity: string
          }
        expect(active.animation, `${sample.channel} subject must own its authored keyframes`)
          .not.toBe('none')
        await page.waitForFunction((channel) => !document.querySelector('.curse-folio')
          ?.classList.contains(`is-motion-${channel}`), sample.channel)
        const settled = await page.locator(sample.subject).evaluate((node) => ({
          transform: getComputedStyle(node).transform,
          opacity: getComputedStyle(node).opacity,
        }))
        expect(settled).not.toEqual(active)
      } finally { await page.close() }
    }

    const page = await open('/tests/game/approved-presentation-fixture.html', { width: 1600, height: 1000 })
    try {
      const source = page.locator('[data-puzzle="completed-seal"]')
      const box = await source.boundingBox()
      if (box === null) throw new Error('completed motion record missing')
      await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2)
      await page.mouse.down()
      await page.mouse.move(1100, 400)
      await page.mouse.up()
      expect(await page.locator('.curse-folio').getAttribute('data-motion-record-kind')).toBe('return')
      await page.waitForFunction(() => !document.querySelector('.curse-folio')
        ?.classList.contains('is-motion-record'))
    } finally { await page.close() }
  })

  it('renders transparent Dark Slate proof pixels with cyan and binder-neon linework', async () => {
    const page = await open('/tests/game/game-proof-surface-fixture.html', { width: 1600, height: 900 })
    try {
      await page.waitForSelector('.curse-game-proof-canvas')
      const palette = await page.locator('.curse-game-proof-canvas').evaluate((node) => {
        const canvas = node as HTMLCanvasElement
        const data = canvas.getContext('2d')!.getImageData(0, 0, canvas.width, canvas.height).data
        let transparent = 0
        let cyan = 0
        let violet = 0
        let lightPaper = 0
        for (let index = 0; index < data.length; index += 4) {
          const r = data[index]!, g = data[index + 1]!, b = data[index + 2]!, a = data[index + 3]!
          if (a === 0) transparent++
          if (a > 48 && g > 145 && b > 150 && g > r * 1.15) cyan++
          if (a > 48 && b > g * 1.12 && r > g * 1.05) violet++
          if (a > 220 && ((r === 250 && g === 247 && b === 238)
            || (r === 232 && g === 228 && b === 216))) lightPaper++
        }
        return {
          background: getComputedStyle(canvas).backgroundColor,
          transparent,
          cyan,
          violet,
          lightPaper,
        }
      })
      expect(palette.background).toBe('rgba(0, 0, 0, 0)')
      expect(palette.transparent).toBeGreaterThan(1000)
      expect(palette.cyan).toBeGreaterThan(20)
      expect(palette.violet).toBeGreaterThan(20)
      expect(palette.lightPaper).toBe(0)
    } finally { await page.close() }
  })
})
