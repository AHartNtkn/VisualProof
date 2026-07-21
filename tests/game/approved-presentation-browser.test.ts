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

type MotionFrame = {
  readonly animation: string
  readonly transform: string
  readonly opacity: string
  readonly duration: string
  readonly x: number
  readonly y: number
}

const armMotionTrace = async (page: Page, channel: string, subject: string): Promise<void> => {
  await page.evaluate(({ channel, subject }) => {
    delete document.documentElement.dataset.presentationMotionTrace
    const root = document.querySelector('.curse-folio')
    if (!(root instanceof HTMLElement)) throw new Error('folio motion root missing')
    let started = false
    const frames: Array<{
      animation: string, transform: string, opacity: string, duration: string, x: number, y: number
    }> = []
    const frame = () => {
      const node = document.querySelector(subject)
      if (node instanceof HTMLElement) {
        const style = getComputedStyle(node)
        const rect = node.getBoundingClientRect()
        frames.push({
          animation: style.animationName,
          transform: style.transform,
          opacity: style.opacity,
          duration: style.animationDuration,
          x: rect.x,
          y: rect.y,
        })
      }
      if (root.classList.contains(`is-motion-${channel}`)) {
        requestAnimationFrame(frame)
      } else {
        document.documentElement.dataset.presentationMotionTrace = JSON.stringify(frames)
      }
    }
    const observer = new MutationObserver(() => {
      if (started || !root.classList.contains(`is-motion-${channel}`)) return
      started = true
      frame()
      observer.disconnect()
    })
    observer.observe(root, { attributes: true })
  }, { channel, subject })
}

const readMotionTrace = async (page: Page): Promise<readonly MotionFrame[]> => {
  await page.waitForFunction(() => document.documentElement
    .dataset.presentationMotionTrace !== undefined)
  return page.evaluate(() => JSON.parse(document.documentElement
    .dataset.presentationMotionTrace!))
}

const expectPaintedMotion = (channel: string, frames: readonly MotionFrame[]): void => {
  expect(frames.length, `${channel} must paint multiple frames`).toBeGreaterThan(1)
  expect(new Set(frames.map(({ transform, opacity, x, y }) =>
    `${transform}|${opacity}|${x.toFixed(2)}|${y.toFixed(2)}`)).size,
  `${channel} must change painted geometry or opacity`).toBeGreaterThan(1)
  expect(frames.some(({ animation }) => animation !== 'none'),
    `${channel} must use authored keyframes`).toBe(true)
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
          sheet: rect('.record-grid'),
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
      expect(result.records).toHaveLength(6)
      expect(result.records.every(({ width, height }) => width > 0 && height > 0)).toBe(true)
      expect(new Set(result.records.map(({ x }) => Math.round(x))).size).toBe(2)
      expect(new Set(result.records.map(({ y }) => Math.round(y))).size).toBe(3)
      expect(result.records.every(({ x, y, width, height }) =>
        x >= result.sheet.x - 1
        && y >= result.sheet.y - 1
        && x + width <= result.sheet.x + result.sheet.width + 1
        && y + height <= result.sheet.y + result.sheet.height + 1)).toBe(true)
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
        await armMotionTrace(page, sample.channel, sample.subject)
        await sample.trigger(page)
        const frames = await readMotionTrace(page)
        expectPaintedMotion(sample.channel, frames)
        const settled = await page.locator(sample.subject).evaluate((node) => ({
          animation: getComputedStyle(node).animationName,
          transform: getComputedStyle(node).transform,
          opacity: getComputedStyle(node).opacity,
          visibility: getComputedStyle(node).visibility,
        }))
        expect(settled.animation).toBe('none')
        if (sample.channel === 'packet') {
          expect(settled).toMatchObject({ opacity: '0', visibility: 'hidden' })
        }
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
      await armMotionTrace(page, 'record', '.inspection-record')
      await page.mouse.up()
      expect(await page.locator('.curse-folio').getAttribute('data-motion-record-kind')).toBe('return')
      expectPaintedMotion('record', await readMotionTrace(page))
      expect(await page.locator('.inspection-stage').getAttribute('aria-hidden')).toBe('true')
    } finally { await page.close() }

    const interrupted = await open('/tests/game/approved-presentation-fixture.html', { width: 1600, height: 1000 })
    try {
      await interrupted.locator('.cover-spine-hit').click()
      await interrupted.waitForTimeout(110)
      const jump = await interrupted.evaluate(() => {
        const surface = document.querySelector('.cover-surface')!.getBoundingClientRect()
        document.querySelector<HTMLElement>('.cover-spine-hit')!.click()
        const replacement = document.querySelector('.cover-surface')!.getBoundingClientRect()
        return Math.hypot(replacement.x - surface.x, replacement.y - surface.y)
      })
      expect(jump).toBeLessThan(1)
    } finally { await interrupted.close() }

    const recordInterrupted = await open(
      '/tests/game/approved-presentation-fixture.html',
      { width: 1600, height: 1000 },
    )
    try {
      const source = recordInterrupted.locator('[data-puzzle="completed-seal"]')
      const box = await source.boundingBox()
      if (box === null) throw new Error('completed reversal record missing')
      await recordInterrupted.mouse.move(box.x + box.width / 2, box.y + box.height / 2)
      await recordInterrupted.mouse.down()
      await recordInterrupted.evaluate(() => window.__approvedPresentationFixture.recordMotion(true))
      await recordInterrupted.waitForTimeout(110)
      const jump = await recordInterrupted.evaluate(() => {
        const before = document.querySelector('.inspection-record')!.getBoundingClientRect()
        window.__approvedPresentationFixture.recordMotion(false)
        const after = document.querySelector('.inspection-record')!.getBoundingClientRect()
        return Math.hypot(after.x - before.x, after.y - before.y)
      })
      expect(jump).toBeLessThan(1)
      await recordInterrupted.evaluate(() => window.__approvedPresentationFixture.settleRecordMotion())
      await recordInterrupted.mouse.up()
    } finally { await recordInterrupted.close() }

    const compactDrag = await open(
      '/tests/game/approved-presentation-fixture.html',
      { width: 760, height: 900 },
    )
    try {
      await compactDrag.evaluate(() => window.__approvedPresentationFixture.setFolioDrawerOpen(true))
      await compactDrag.waitForTimeout(80)
      const source = compactDrag.locator('[data-puzzle="completed-seal"]')
      const box = await source.boundingBox()
      if (box === null) throw new Error('compact moving record missing')
      const pointer = { x: box.x + box.width / 2, y: box.y + box.height / 2 }
      await compactDrag.mouse.move(pointer.x, pointer.y)
      await compactDrag.mouse.down()
      const lifted = await compactDrag.locator('.inspection-positioner.is-artifact-lifted')
        .boundingBox()
      if (lifted === null) throw new Error('compact moving lift missing')
      expect(Math.hypot(
        lifted.x + lifted.width / 2 - pointer.x,
        lifted.y + lifted.height / 2 - pointer.y,
      )).toBeLessThan(1)
      await compactDrag.mouse.up()
    } finally { await compactDrag.close() }

    const reduced = await open('/tests/game/approved-presentation-fixture.html?reduced', { width: 1600, height: 1000 })
    try {
      await armMotionTrace(reduced, 'dossier', '.active-dossier')
      await reduced.evaluate(() => window.__approvedPresentationFixture.dossier())
      const frames = await readMotionTrace(reduced)
      expect(frames.some(({ animation }) => animation === 'reduced-depth')).toBe(true)
      expect(frames.some(({ duration }) => duration === '0.09s')).toBe(true)
      expect(new Set(frames.map(({ x, y, transform }) => `${x.toFixed(2)}|${y.toFixed(2)}|${transform}`)).size)
        .toBe(1)
    } finally { await reduced.close() }
  })

  it('renders the real controller with the approved timeline and Dark Slate neon proof palette', async () => {
    const page = await open('/tests/game/authoritative-runtime-fixture.html?scenario=editor', { width: 1600, height: 1000 })
    try {
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture?.ready === true)
      expect(await page.locator('.curse-production-timeline').evaluate((node) =>
        getComputedStyle(node).visibility)).toBe('visible')
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      await page.waitForSelector('.curse-game-proof-canvas')
      await page.waitForFunction(() => {
        const canvas = document.querySelector<HTMLCanvasElement>('.curse-game-proof-canvas')
        if (canvas === null || canvas.width === 0 || canvas.height === 0) return false
        const data = canvas.getContext('2d')!.getImageData(0, 0, canvas.width, canvas.height).data
        for (let index = 3; index < data.length; index += 4) if (data[index]! > 0) return true
        return false
      })
      const palette = await page.locator('.curse-game-proof-canvas').evaluate((node) => {
        const canvas = node as HTMLCanvasElement
        const data = canvas.getContext('2d')!.getImageData(0, 0, canvas.width, canvas.height).data
        let transparent = 0
        let cyan = 0
        let violet = 0
        let lightPaper = 0
        let darkField = 0
        for (let index = 0; index < data.length; index += 4) {
          const r = data[index]!, g = data[index + 1]!, b = data[index + 2]!, a = data[index + 3]!
          if (a === 0) transparent++
          if (a > 48 && g > 145 && b > 150 && g > r * 1.15) cyan++
          if (a > 48 && b > g * 1.12 && r > g * 1.05) violet++
          if (a > 4 && r < 80 && g < 90 && b < 100) darkField++
          if (a > 220 && ((r === 250 && g === 247 && b === 238)
            || (r === 232 && g === 228 && b === 216))) lightPaper++
        }
        return {
          background: getComputedStyle(canvas).backgroundColor,
          transparent,
          cyan,
          violet,
          lightPaper,
          darkField,
        }
      })
      const slider = page.locator('.curse-production-timeline-control')
      const handleCenter = async () => page.locator('.curse-production-timeline-handle')
        .evaluate((node) => {
          const rect = node.getBoundingClientRect()
          return rect.x + rect.width / 2
        })
      await page.evaluate(() => {
        window.__authoritativeRuntimeFixture.witness(0)
        window.__authoritativeRuntimeFixture.witness(1)
      })
      await page.evaluate(() => window.__authoritativeRuntimeFixture.settle())
      await page.waitForFunction(() => !window.__authoritativeRuntimeFixture.state().motionPlaying)
      const end = await handleCenter()
      await page.evaluate(() => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'moveTimeline', cursor: 0 }))
      const start = await handleCenter()
      const rail = await slider.boundingBox()
      if (rail === null) throw new Error('production timeline rail missing')
      await slider.click({ position: {
        x: start + (end - start) / 2 - rail.x,
        y: rail.height / 2,
      } })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)
      expect(await handleCenter()).toBeCloseTo(start + (end - start) / 2, 1)
      expect(palette.background).toBe('rgba(0, 0, 0, 0)')
      expect(palette.transparent).toBeGreaterThan(1000)
      expect(palette.cyan).toBeGreaterThan(20)
      expect(palette.violet).toBeGreaterThan(20)
      expect(palette.lightPaper).toBe(0)
      expect(palette.darkField).toBeGreaterThan(20)
    } finally { await page.close() }
  })
})
