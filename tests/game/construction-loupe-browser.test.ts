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
  if (address === null || address === undefined || typeof address === 'string') throw new Error('Vite did not expose a loupe fixture address')
  fixtureUrl = `http://127.0.0.1:${address.port}/tests/game/construction-loupe-fixture.html`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

const openFixture = async (viewport = { width: 1200, height: 820 }): Promise<Page> => {
  const page = await browser.newPage({ viewport })
  await page.goto(fixtureUrl)
  await page.waitForSelector('.cursebreaker-construction-loupe', { timeout: 5_000 })
  return page
}

describe('rendered circular construction loupe', () => {
  it('keeps the aperture pointer-reachable through an exact SVG annular rim', async () => {
    const page = await openFixture()
    try {
      const hit = await page.evaluate(() => {
        const root = document.querySelector<HTMLElement>('.cursebreaker-construction-loupe')!
        const rect = root.getBoundingClientRect()
        const center = document.elementFromPoint(rect.left + rect.width / 2, rect.top + rect.height / 2)
        const rimX = rect.left + rect.width * .995
        const rimY = rect.top + rect.height / 2
        const rim = document.elementFromPoint(rimX, rimY)
        return {
          center: center?.className,
          rim: typeof rim?.className === 'string' ? rim.className : rim?.getAttribute('class'),
          rimStack: document.elementsFromPoint(rimX, rimY).map((node) => typeof node.className === 'string' ? node.className : node.getAttribute('class')),
          rootWidth: rect.width,
          rootHeight: rect.height,
          rimShape: root.querySelector('.cursebreaker-construction-loupe__rim-hit-stroke')?.tagName,
        }
      })
      expect(hit).toMatchObject({
        center: 'cursebreaker-construction-loupe__canvas',
        rim: 'cursebreaker-construction-loupe__rim-hit-stroke',
        rimShape: 'circle',
      })
      expect(hit.rootWidth).toBeCloseTo(hit.rootHeight, 4)
    } finally { await page.close() }
  })

  it('renders only semantic layers and hidden instructions, with no standard actions or title/menu', async () => {
    const page = await openFixture()
    try {
      const state = await page.locator('.cursebreaker-construction-loupe').evaluate((root) => ({
        buttons: root.querySelectorAll('button').length,
        headers: root.querySelectorAll('header').length,
        menus: root.querySelectorAll('[role="menu"]').length,
        instructionClip: getComputedStyle(root.querySelector('.cursebreaker-construction-loupe__instructions')!).clipPath,
        opticsPointer: getComputedStyle(root.querySelector('.cursebreaker-construction-loupe__art--optics')!).pointerEvents,
        images: [...root.querySelectorAll('img')].map((image) => ({ width: image.naturalWidth, height: image.naturalHeight })),
      }))
      expect(state).toMatchObject({ buttons: 0, headers: 0, menus: 0, opticsPointer: 'none' })
      expect(state.instructionClip).not.toBe('none')
      expect(state.images).toEqual(Array.from({ length: 3 }, () => ({ width: 1400, height: 1400 })))
    } finally { await page.close() }
  })

  it('moves by the rim, resizes proportionally by the terminal, and keeps the terminal reachable', async () => {
    const page = await openFixture()
    try {
      const root = page.locator('.cursebreaker-construction-loupe')
      const before = await root.boundingBox()
      if (before === null) throw new Error('loupe has no box')
      await page.mouse.move(before.x + before.width * .995, before.y + before.height / 2)
      await page.mouse.down()
      await page.mouse.move(before.x + before.width * .995 + 80, before.y + before.height / 2 + 30)
      await page.mouse.up()
      const moved = await root.boundingBox()
      if (moved === null) throw new Error('moved loupe has no box')
      expect(moved.width).toBeCloseTo(before.width, 2)
      expect(moved.x).toBeGreaterThan(before.x + 60)

      const terminal = page.locator('.cursebreaker-construction-loupe__terminal-hit')
      const terminalBefore = await terminal.boundingBox()
      if (terminalBefore === null) throw new Error('terminal has no box')
      await page.mouse.move(terminalBefore.x + terminalBefore.width / 2, terminalBefore.y + terminalBefore.height / 2)
      await page.mouse.down()
      await page.mouse.move(terminalBefore.x + 90, terminalBefore.y + 90)
      await page.mouse.up()
      const resized = await root.boundingBox()
      const terminalAfter = await terminal.boundingBox()
      if (resized === null || terminalAfter === null) throw new Error('resized loupe geometry missing')
      expect(resized.width).toBeGreaterThan(moved.width)
      expect(resized.width).toBeCloseTo(resized.height, 2)
      expect(terminalAfter.x).toBeGreaterThanOrEqual(0)
      expect(terminalAfter.y).toBeGreaterThanOrEqual(0)
      expect(terminalAfter.x + terminalAfter.width).toBeLessThanOrEqual(1200)
      expect(terminalAfter.y + terminalAfter.height).toBeLessThanOrEqual(820)
    } finally { await page.close() }
  })

  it('keeps the right-click spawn cascade and keyboard lifecycle', async () => {
    const page = await openFixture()
    try {
      const canvas = page.locator('.cursebreaker-construction-loupe__canvas')
      await canvas.click({ button: 'right', position: { x: 260, y: 260 } })
      await expect.poll(() => page.locator('.vpa-spawn-cascade').count()).toBe(1)
      await page.keyboard.press('Escape')
      await page.keyboard.press('Escape')
      await expect.poll(() => page.locator('.cursebreaker-construction-loupe').count()).toBe(0)
      expect(await page.evaluate(() => window.__constructionLoupeFixture.closed)).toBe(1)

      await page.evaluate(() => window.__constructionLoupeFixture.reopen())
      await page.locator('.cursebreaker-construction-loupe__canvas').focus()
      await page.keyboard.press('Enter')
      expect(await page.evaluate(() => window.__constructionLoupeFixture.commits)).toBe(1)
      expect(await page.evaluate(() => window.__constructionLoupeFixture.lastRule)).toBe('comprehensionInstantiate')
      expect(await page.locator('.cursebreaker-construction-loupe').count()).toBe(0)
    } finally { await page.close() }
  })

  it('does not let Backspace close while the spawn search text entry is active', async () => {
    const page = await openFixture()
    try {
      const canvas = page.locator('.cursebreaker-construction-loupe__canvas')
      await canvas.click({ button: 'right', position: { x: 260, y: 260 } })
      const search = page.locator('.vpa-spawn-search')
      await search.fill('abc')
      await page.keyboard.press('Backspace')
      expect(await page.locator('.cursebreaker-construction-loupe').count()).toBe(1)
      expect(await search.inputValue()).toBe('ab')
    } finally { await page.close() }
  })

  it('maps the rendered canvas exactly and limits reduced motion to decoration', async () => {
    const page = await openFixture()
    try {
      const root = page.locator('.cursebreaker-construction-loupe')
      const before = await root.boundingBox()
      const mapping = await page.evaluate(() => window.__constructionLoupeFixture.centerMapping())
      expect(mapping.screen.x).toBeCloseTo(mapping.canvas.width / 2, 6)
      expect(mapping.screen.y).toBeCloseTo(mapping.canvas.height / 2, 6)
      await page.evaluate(() => window.__constructionLoupeFixture.setReducedMotion(true))
      expect(await root.evaluate((node) => node.classList.contains('is-reduced-motion'))).toBe(true)
      expect(await page.locator('.cursebreaker-construction-loupe__art--optics').evaluate(
        (node) => getComputedStyle(node).transitionDuration,
      )).toBe('0s')
      expect(await root.boundingBox()).toEqual(before)
    } finally { await page.close() }
  })

  it('keeps history shortcuts local and leaves proof-only F inert while the loupe owns input', async () => {
    const page = await openFixture()
    try {
      const canvas = page.locator('.cursebreaker-construction-loupe__canvas')
      await canvas.click({ button: 'right', position: { x: 260, y: 260 } })
      await page.getByRole('button', { name: /λ term/ }).click()
      await page.locator('.vpa-spawn-search').fill('x')
      await page.keyboard.press('Enter')
      expect(await page.evaluate(() => window.__constructionLoupeFixture.history())).toEqual({ cursor: 1, length: 2 })

      await page.keyboard.press('Control+z')
      expect(await page.evaluate(() => window.__constructionLoupeFixture.history())).toEqual({ cursor: 0, length: 2 })
      await page.keyboard.press('Control+Shift+z')
      expect(await page.evaluate(() => window.__constructionLoupeFixture.history())).toEqual({ cursor: 1, length: 2 })
      await page.keyboard.press('F')
      expect(await page.evaluate(() => window.__constructionLoupeFixture.history())).toEqual({ cursor: 1, length: 2 })
      await page.evaluate(() => window.dispatchEvent(new KeyboardEvent('keydown', { key: 'F', repeat: true })))
      expect(await page.evaluate(() => window.__constructionLoupeFixture.history())).toEqual({ cursor: 1, length: 2 })
    } finally { await page.close() }
  })
})

declare global {
  interface Window {
    __constructionLoupeFixture: {
      closed: number
      commits: number
      lastRule: string | null
      reopen(): void
      setReducedMotion(enabled: boolean): void
      centerMapping(): { readonly screen: { readonly x: number; readonly y: number }; readonly canvas: { readonly width: number; readonly height: number } }
      history(): { readonly cursor: number; readonly length: number }
    }
  }
}
