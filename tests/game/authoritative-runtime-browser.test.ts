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
    throw new Error('Vite did not expose the authoritative runtime fixture')
  }
  fixtureUrl = `http://127.0.0.1:${address.port}/tests/game/authoritative-runtime-fixture.html`
  browser = await chromium.launch()
})

afterAll(async () => {
  await browser?.close()
  await server?.close()
})

const openFixture = async (
  scenario = 'null',
  reducedMotion?: 'reduce' | 'no-preference',
): Promise<Page> => {
  const page = await browser.newPage({ viewport: { width: 1400, height: 900 } })
  if (reducedMotion !== undefined) await page.emulateMedia({ reducedMotion })
  await page.goto(`${fixtureUrl}?scenario=${scenario}`)
  await page.waitForFunction(() => window.__authoritativeRuntimeFixture?.ready === true)
  return page
}

describe('authoritative production renderer runtime', () => {
  it('starts a null save in a visible, operable archive around the empty substrate', async () => {
    const page = await openFixture()
    try {
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        mode: 'archive', activePuzzle: null, substrateSeed: 'cursebreaker:archive:empty',
        hasProof: false, hasTimeline: false,
      })
      expect(await page.locator('.curse-production-environment').count()).toBe(1)
      expect(await page.locator('.curse-folio').count()).toBe(1)
      expect(await page.locator('.curse-folio-record[data-status="unlocked"]').count())
        .toBeGreaterThan(0)
      expect(await page.locator('.curse-game-proof-canvas').count()).toBe(0)
      const timeline = page.locator('.curse-production-timeline-control')
      expect(await timeline.count()).toBe(1)
      expect(await timeline.getAttribute('aria-disabled')).toBe('true')
      expect(await timeline.getAttribute('tabindex')).toBe('-1')
      expect(await page.locator('.curse-production-timeline-handle-slot').evaluate((node) =>
        getComputedStyle(node).getPropertyValue('--curse-timeline-position').trim())).toBe('0')
      expect(await page.locator('.curse-production-timeline').evaluate((node) =>
        getComputedStyle(node).visibility)).toBe('visible')
      expect(await page.locator('.curse-production-timeline-housing').count()).toBe(1)
      expect(await page.locator('.curse-production-timeline-handle').count()).toBe(1)
    } finally { await page.close() }
  })

  it('keeps one slider identity through archive, puzzle, completion, and archive return', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => {
        (window as any).__persistentTimeline = document.querySelector(
          '.curse-production-timeline-control',
        )
      })
      await page.locator('.curse-production-timeline-control').evaluate((node) => {
        node.dispatchEvent(new KeyboardEvent('keydown', {
          key: 'End', bubbles: true, cancelable: true,
        }))
        node.dispatchEvent(new PointerEvent('pointerdown', {
          pointerId: 71, button: 0, clientX: 500, bubbles: true, cancelable: true,
        }))
      })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes())).toEqual([])

      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      expect(await page.evaluate(() => (window as any).__persistentTimeline === document.querySelector(
        '.curse-production-timeline-control',
      ))).toBe(true)
      expect(await page.locator('.curse-production-timeline-control').getAttribute('aria-disabled'))
        .toBe('false')

      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.witness(1)
        fixture.witness(2)
      })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('completion')
      expect(await page.evaluate(() => (window as any).__persistentTimeline === document.querySelector(
        '.curse-production-timeline-control',
      ))).toBe(true)
      expect(await page.locator('.curse-production-timeline-control').getAttribute('aria-disabled'))
        .toBe('true')
      expect(await page.locator('.curse-production-timeline-handle-slot').evaluate((node) =>
        getComputedStyle(node).getPropertyValue('--curse-timeline-position').trim())).toBe('1')

      await page.getByRole('button', { name: 'Return to level selection' }).click()
      expect(await page.evaluate(() => (window as any).__persistentTimeline === document.querySelector(
        '.curse-production-timeline-control',
      ))).toBe(true)
      expect(await page.locator('.curse-production-timeline-control').getAttribute('aria-disabled'))
        .toBe('true')
      expect(await page.locator('.curse-production-timeline-handle-slot').evaluate((node) =>
        getComputedStyle(node).getPropertyValue('--curse-timeline-position').trim())).toBe('0')
    } finally { await page.close() }
  })

  it('keeps the same inert folio and record positions visible beneath completion', async () => {
    const page = await openFixture()
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.evaluate(() => {
        (window as any).__persistentCompletionFolio = document.querySelector('.curse-folio')
      })
      const before = await page.locator(`[data-puzzle="${first}"]`).boundingBox()
      if (before === null) throw new Error('first folio record has no initial bounds')
      await page.locator(`[data-puzzle="${first}"]`).click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.witness(1)
        fixture.witness(2)
      })
      await page.waitForSelector('.curse-completion')

      expect(await page.evaluate(() =>
        (window as any).__persistentCompletionFolio === document.querySelector('.curse-folio')))
        .toBe(true)
      const record = page.locator(`[data-puzzle="${first}"]`)
      expect(await record.getAttribute('data-status')).toBe('completed')
      expect(await record.getAttribute('data-affordance')).toBe('inert')
      const after = await record.boundingBox()
      if (after === null) throw new Error('completed folio record disappeared')
      expect(after).toEqual(before)
      const stateBeforeClick = await page.evaluate(() => window.__authoritativeRuntimeFixture.state())
      await record.click({ force: true })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state()))
        .toEqual(stateBeforeClick)
    } finally { await page.close() }
  })

  it('renders the approved desktop workspace rectangles at both reference viewports', async () => {
    const page = await openFixture()
    try {
      await page.waitForFunction(() => Array.from(
        document.querySelectorAll<HTMLImageElement>('.curse-decoration'),
      ).every((image) => image.complete && image.naturalWidth > 0))

      const assertRectangles = async (
        viewport: { width: number, height: number },
        expected: { lensLeft: number, folioWidth: number },
      ): Promise<void> => {
        await page.setViewportSize(viewport)
        await page.waitForFunction(({ lensLeft, lensSize }) => {
          const lens = document.querySelector<HTMLElement>('.curse-production-lens')
            ?.getBoundingClientRect()
          return lens !== undefined
            && Math.abs(lens.left - lensLeft) < 1
            && Math.abs(lens.top) < 1
            && Math.abs(lens.width - lensSize) < 1
            && Math.abs(lens.height - lensSize) < 1
        }, { lensLeft: expected.lensLeft, lensSize: viewport.height })

        const rectangles = await page.evaluate(() => {
          const rectangle = (selector: string): Record<'x' | 'y' | 'width' | 'height', number> => {
            const node = document.querySelector<HTMLElement>(selector)
            if (node === null) throw new Error(`workspace geometry node missing: ${selector}`)
            const { x, y, width, height } = node.getBoundingClientRect()
            return { x, y, width, height }
          }
          return {
            lens: rectangle('.curse-production-lens'),
            folio: rectangle('.curse-production-folio-host'),
            aperture: rectangle('.curse-production-aperture'),
            gasket: rectangle('.curse-production-gasket'),
            timeline: rectangle('.curse-production-timeline'),
            timelineHousing: rectangle('.curse-production-timeline-housing'),
            timelineHandleLayer: rectangle('.curse-production-timeline-handle-slot'),
          }
        })
        expect(rectangles.lens).toEqual({
          x: expected.lensLeft,
          y: 0,
          width: viewport.height,
          height: viewport.height,
        })
        expect(rectangles.folio.x).toBe(0)
        expect(rectangles.folio.y).toBe(0)
        expect(rectangles.folio.width).toBeCloseTo(expected.folioWidth, 0)
        expect(rectangles.folio.height).toBe(viewport.height)
        expect(rectangles.aperture.x).toBeCloseTo(
          expected.lensLeft + viewport.height * 0.1362,
          0,
        )
        expect(rectangles.aperture.y).toBeCloseTo(viewport.height * 0.0757, 0)
        expect(rectangles.aperture.width).toBeCloseTo(viewport.height * 0.7276, 0)
        expect(rectangles.aperture.height).toBeCloseTo(viewport.height * 0.7278, 0)
        expect(rectangles.gasket).toEqual(rectangles.lens)
        expect(rectangles.timeline).toEqual(rectangles.lens)
        expect(rectangles.timelineHousing).toEqual(rectangles.lens)
        expect(rectangles.timelineHandleLayer).toEqual(rectangles.lens)
      }

      await assertRectangles(
        { width: 1600, height: 1000 },
        { lensLeft: 600, folioWidth: Math.min(736.2, 628.8) },
      )
      await assertRectangles(
        { width: 1920, height: 1080 },
        { lensLeft: 840, folioWidth: Math.min(987.096, 871.104) },
      )
    } finally { await page.close() }
  })

  it('renders the approved physical folio layers and first six records as two columns by three rows', async () => {
    const page = await openFixture('long')
    try {
      await page.setViewportSize({ width: 1600, height: 1000 })
      const presentation = await page.evaluate(() => {
        const root = document.querySelector<HTMLElement>('.curse-folio')
        if (root === null) throw new Error('physical folio root missing')
        const records = Array.from(root.querySelectorAll<HTMLElement>('.curse-folio-record'))
          .slice(0, 6)
          .map((record) => {
            const { x, y, width, height } = record.getBoundingClientRect()
            return { x, y, width, height }
          })
        const count = (selector: string): number => root.querySelectorAll(selector).length
        return {
          counts: {
            lowerBoard: count('.folio-board-lower'),
            underlays: count('.dossier-underlay'),
            guardLeaf: count('.guard-leaf-layer'),
            activeDossier: count('.active-dossier'),
            cover: count('.folio-cover'),
            stage: count('.inspection-stage'),
            sheet: count('.record-grid'),
          },
          records,
        }
      })
      expect(presentation.counts).toEqual({
        lowerBoard: 1,
        underlays: 2,
        guardLeaf: 1,
        activeDossier: 1,
        cover: 1,
        stage: 1,
        sheet: 1,
      })
      expect(presentation.records).toHaveLength(6)
      const columns = [...new Set(presentation.records.map(({ x }) => Math.round(x)))]
      const rows = [...new Set(presentation.records.map(({ y }) => Math.round(y)))]
      expect(columns).toHaveLength(2)
      expect(rows).toHaveLength(3)
      expect(presentation.records.every(({ width, height }) => width > 0 && height > 0))
        .toBe(true)
    } finally { await page.close() }
  })

  it('restores an active puzzle save exactly before mounting its stateful views', async () => {
    const page = await openFixture('restore')
    try {
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        mode: 'puzzle', activePuzzle: 'first-artifact', cursor: 1,
        substrateSeed: expect.stringMatching(/^cursebreaker:puzzle:first-artifact:/),
        selectedScroll: 137,
        settings: { reducedMotion: true, fullscreen: false, textSize: 'large' },
        hasProof: true, hasTimeline: true,
      })
      expect(await page.locator('.curse-production-environment').getAttribute('data-text-size')).toBe('large')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes())).toEqual([])
    } finally { await page.close() }
  })

  it('restores a persisted completion into the dedicated success surface', async () => {
    const page = await openFixture('completion')
    try {
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        mode: 'completion',
        hasProof: false,
        hasTimeline: false,
      })
      const completion = page.locator('.curse-completion')
      expect(await completion.count()).toBe(1)
      expect(await completion.locator('h1').textContent()).toBe('first-artifact professional name')
      expect(await completion.locator('[data-completion-moves]').textContent()).toBe('3 moves')
      expect(await completion.locator('button').allTextContents()).toEqual([
        'Return to level selection',
      ])
      expect(await page.locator('.curse-production-timeline-housing').count()).toBe(1)
      expect(await page.locator('.curse-production-timeline-handle').count()).toBe(1)
      expect(await page.locator('.curse-production-timeline-control').count()).toBe(1)
      expect(await page.locator('.curse-production-timeline-control').getAttribute('aria-disabled'))
        .toBe('true')
      const folio = page.locator('.curse-folio')
      expect(await folio.count()).toBe(1)
      expect(await folio.getAttribute('data-mode')).toBe('completion')
      expect(await folio.getAttribute('data-cover')).toBe('open')
      const completedRecord = folio.locator('[data-puzzle="first-artifact"]')
      expect(await completedRecord.getAttribute('data-status')).toBe('completed')
      expect(await completedRecord.getAttribute('data-affordance')).toBe('inert')
      await completion.locator('button').click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('archive')
      expect(await folio.count()).toBe(1)
    } finally { await page.close() }
  })

  it('uses Released mount as the sole completion treatment', async () => {
    const page = await openFixture('completion')
    try {
      const presentation = page.locator('.curse-game-presentation')
      const completion = page.locator('.curse-completion')
      const style = await completion.evaluate((node) => {
        const computed = getComputedStyle(node)
        return {
          borderLeftWidth: computed.borderLeftWidth,
          borderRadius: computed.borderRadius,
          boxShadow: computed.boxShadow,
        }
      })
      expect(await presentation.getAttribute('data-completion-candidate')).toBeNull()
      expect(style.borderLeftWidth).toBe('17px')
      expect(style.borderRadius).toBe('4.8px')
      expect(style.boxShadow).not.toBe('none')
      expect(await completion.locator('[data-completion-line]').textContent())
        .toBe('Restoration complete')
      expect(await completion.locator('h1').textContent())
        .toBe('first-artifact professional name')
      expect(await completion.locator('[data-completion-moves]').textContent()).toBe('3 moves')
      expect(await completion.locator('[data-completion-response]').textContent()).not.toBe('')
      expect(await completion.locator('button').allTextContents())
        .toEqual(['Return to level selection'])
      expect(await page.locator('.curse-production-timeline-control').getAttribute('aria-disabled'))
        .toBe('true')
      await completion.locator('button').click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('archive')
    } finally { await page.close() }
  })

  it('applies the saved interface text size to rendered game text', async () => {
    const page = await openFixture()
    try {
      const renderedSize = async (): Promise<number> => page.locator('.curse-folio-record-name')
        .first()
        .evaluate((record) => Number.parseFloat(getComputedStyle(record).fontSize))
      const medium = await renderedSize()
      await page.evaluate(() => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'setTextSize', value: 'large' }))
      const large = await renderedSize()
      expect(large).toBeGreaterThan(medium)
    } finally { await page.close() }
  })

  it('lets compact large-text records grow inside the continuous scrolling sheet', async () => {
    const page = await openFixture('opening')
    try {
      await page.setViewportSize({ width: 760, height: 900 })
      await page.evaluate(() => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'setTextSize', value: 'large' }))
      const records = await page.locator('.curse-folio-record').evaluateAll((nodes) => nodes
        .map((node) => ({
          clientHeight: (node as HTMLElement).clientHeight,
          scrollHeight: (node as HTMLElement).scrollHeight,
          faceClientHeight: (node.querySelector('.record-face') as HTMLElement).clientHeight,
          faceScrollHeight: (node.querySelector('.record-face') as HTMLElement).scrollHeight,
        })))
      expect(records).not.toHaveLength(0)
      expect(records.every(({ clientHeight, scrollHeight, faceClientHeight, faceScrollHeight }) =>
        scrollHeight <= clientHeight + 1 && faceScrollHeight <= faceClientHeight + 1)).toBe(true)
      expect(await page.locator('.record-grid').evaluate((sheet) =>
        (sheet as HTMLElement).scrollHeight > (sheet as HTMLElement).clientHeight)).toBe(true)
    } finally { await page.close() }
  })

  it('quarantines a malformed save, installs a current replacement, and opens the archive', async () => {
    const page = await openFixture('corrupt')
    try {
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.launchError()))
        .toBeNull()
      expect(await page.locator('.curse-production-environment').count()).toBe(1)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('archive')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes())).toEqual([])
      const replacements = await page.evaluate(() =>
        window.__authoritativeRuntimeFixture.invalidSaveReplacements())
      expect(replacements).toHaveLength(1)
      expect(replacements[0]).toMatchObject({ format: 'cursebreaker-save', version: 4, mode: 'archive' })
    } finally { await page.close() }
  })

  it('does not disguise an unexpected decoder fault as a rejected save', async () => {
    const page = await openFixture('decoder-fault')
    try {
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.launchError()))
        .toMatch(/Could not restore the game save: fixture decoder fault/)
      expect(await page.evaluate(() =>
        window.__authoritativeRuntimeFixture.invalidSaveReplacements())).toEqual([])
      expect(await page.locator('.curse-production-environment').count()).toBe(0)
    } finally { await page.close() }
  })

  it('serializes every changed state write and reconciles authoritative fullscreen without looping', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.gateWrites(true)
        fixture.setFullscreenResult(true)
        fixture.dispatch({ kind: 'setTextSize', value: 'large' })
        fixture.dispatch({ kind: 'setReducedMotion', value: true })
        fixture.dispatch({ kind: 'setFullscreen', value: false })
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 1)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)).toBe(1)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(0))
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 2)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(1))
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 3)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(2))
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 4)
      expect(await page.evaluate(() => ({
        fullscreen: window.__authoritativeRuntimeFixture.state().settings.fullscreen,
        requests: window.__authoritativeRuntimeFixture.fullscreenRequests(),
        writes: window.__authoritativeRuntimeFixture.writes().map((save: any) => save.settings),
      }))).toEqual({
        fullscreen: true,
        requests: [false],
        writes: [
          { reducedMotion: false, fullscreen: true, textSize: 'large' },
          { reducedMotion: true, fullscreen: true, textSize: 'large' },
          { reducedMotion: true, fullscreen: false, textSize: 'large' },
          { reducedMotion: true, fullscreen: true, textSize: 'large' },
        ],
      })
      await page.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(3))
      await page.evaluate(() => window.__authoritativeRuntimeFixture.settle())
    } finally { await page.close() }
  })

  it('waits for the latest queued save before both menu and native exit', async () => {
    const menu = await openFixture()
    try {
      await menu.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.gateWrites(true)
        fixture.dispatch({ kind: 'setTextSize', value: 'large' })
        fixture.dispatch({ kind: 'escape' })
        fixture.dispatch({ kind: 'exitGame' })
      })
      await menu.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 1)
      expect(await menu.evaluate(() => window.__authoritativeRuntimeFixture.exits())).toEqual([])
      await menu.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(0))
      await menu.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 2)
      expect(await menu.evaluate(() => window.__authoritativeRuntimeFixture.exits())).toEqual([])
      await menu.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(1))
      await menu.waitForFunction(() => window.__authoritativeRuntimeFixture.exits().length === 1)
      expect(await menu.evaluate(() => (window.__authoritativeRuntimeFixture.exits()[0] as any).settings.textSize)).toBe('large')
    } finally { await menu.close() }

    const native = await openFixture()
    try {
      await native.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.gateWrites(true)
        fixture.dispatch({ kind: 'setReducedMotion', value: true })
        fixture.nativeExit()
      })
      await native.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 1)
      expect(await native.evaluate(() => window.__authoritativeRuntimeFixture.exits())).toEqual([])
      await native.evaluate(() => window.__authoritativeRuntimeFixture.releaseWrite(0))
      await native.waitForFunction(() => window.__authoritativeRuntimeFixture.exits().length === 1)
      expect(await native.evaluate(() => (window.__authoritativeRuntimeFixture.exits()[0] as any).settings.reducedMotion)).toBe(true)
    } finally { await native.close() }
  })

  it('keeps a failed save observable, prevents overtaking writes, and refuses exit success', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.gateWrites(true)
        fixture.dispatch({ kind: 'setTextSize', value: 'large' })
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.writes().length === 1)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.failWrite(0, 'disk unavailable'))
      await expect(page.evaluate(() => window.__authoritativeRuntimeFixture.settle())).rejects.toThrow(/disk unavailable/)
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.dispatch({ kind: 'setReducedMotion', value: true })
        fixture.nativeExit()
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.state().saveFailure !== null)
      expect(await page.evaluate(() => ({
        writes: window.__authoritativeRuntimeFixture.writes().length,
        exits: window.__authoritativeRuntimeFixture.exits().length,
        failure: window.__authoritativeRuntimeFixture.state().saveFailure,
      }))).toEqual({ writes: 1, exits: 0, failure: 'disk unavailable' })
    } finally { await page.close() }
  })

  it('selects archive records, resumes unfinished attempts and replays, and starts a fresh cleared replay', async () => {
    const page = await openFixture()
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      await page.evaluate(() => window.__authoritativeRuntimeFixture.witness(0))
      await page.evaluate(() => window.__authoritativeRuntimeFixture.dispatch({ kind: 'levelSelection' }))
      await page.locator(`[data-puzzle="${first}"]`).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)

      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(1)
        fixture.witness(2)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await page.locator(`[data-puzzle="${first}"]`).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(0)
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await page.locator(`[data-puzzle="${first}"]`).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(1)
        fixture.witness(2)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await page.locator(`[data-puzzle="${first}"]`).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(0)
    } finally { await page.close() }
  })

  it('rewinds to zero, branches, and reconciles the same proof and timeline without remounting', async () => {
    const page = await openFixture()
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.witness(1)
      })
      const before = await page.evaluate(() => window.__authoritativeRuntimeFixture.state())
      await page.locator('.curse-production-timeline-control').focus()
      await page.keyboard.press('Home')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        cursor: 0, proofInstance: before.proofInstance,
      })
      await page.evaluate(() => window.__authoritativeRuntimeFixture.witness(2))
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        cursor: 1,
        steps: ['doubleCutElim'],
        proofInstance: before.proofInstance,
      })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().proofRebuilds))
        .toBeGreaterThan(before.proofRebuilds!)
    } finally { await page.close() }
  })

  it('restores independent culture scroll and changes to the actual compact drawer on resize', async () => {
    const page = await openFixture()
    try {
      const cultures = await page.locator('.curse-folio-culture-tab').all()
      expect(cultures.length).toBe(2)
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        const current = fixture.state().selectedCulture
        fixture.dispatch({ kind: 'setCultureScroll', culture: current, scroll: 71 } as any)
      })
      await cultures[1]!.click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.dispatch({ kind: 'setCultureScroll', culture: fixture.state().selectedCulture, scroll: 143 } as any)
      })
      await cultures[0]!.click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().selectedScroll)).toBe(71)
      await page.setViewportSize({ width: 760, height: 900 })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.state().layout.kind === 'compact')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().layout)).toMatchObject({
        kind: 'compact', folioPresentation: 'drawer',
      })
      const toggle = page.locator('.curse-production-folio-drawer-toggle')
      await expect(toggle.getAttribute('aria-expanded')).resolves.toBe('false')
      await toggle.click()
      await expect(toggle.getAttribute('aria-expanded')).resolves.toBe('true')
      const firstRecord = page.locator('.curse-folio-record').first()
      const recordBounds = await firstRecord.boundingBox()
      if (recordBounds === null) throw new Error('opened compact folio has no record bounds')
      expect(recordBounds.x + recordBounds.width / 2).toBeGreaterThan(0)
      expect(recordBounds.x + recordBounds.width / 2).toBeLessThan(760)
      await firstRecord.click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode)).toBe('puzzle')
      await expect(toggle.getAttribute('aria-expanded')).resolves.toBe('false')
    } finally { await page.close() }
  })

  it('gives proof/timeline focus exact ownership and routes global Escape without remounting', async () => {
    const page = await openFixture()
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.witness(1)
      })
      await page.locator('.record-grid').focus()
      await page.keyboard.press('Control+Z')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(2)
      await page.locator('.curse-game-proof-canvas').focus()
      await page.keyboard.press('Control+Z')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)
      const instance = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().proofInstance)
      await page.keyboard.press('Escape')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toEqual({
        kind: 'pause', presentation: 'menu',
      })
      const pause = page.locator('.curse-pause-menu')
      expect(await pause.count()).toBe(1)
      expect(await pause.getAttribute('role')).toBe('dialog')
      expect(await pause.locator('button').allTextContents()).toEqual([
        'Resume',
        'Level selection',
        'Settings',
        'Exit game',
      ])
      expect(await page.locator('.curse-game-proof-canvas').count()).toBe(1)
      await pause.locator('button', { hasText: 'Settings' }).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toEqual({
        kind: 'pause', presentation: 'settings',
      })
      const settings = page.locator('.curse-pause-settings')
      expect(await settings.count()).toBe(1)
      expect(await settings.locator('[data-setting="reduced-motion"]').count()).toBe(1)
      expect(await settings.locator('[data-setting="fullscreen"]').count()).toBe(1)
      expect(await settings.locator('[data-setting="text-size"]').count()).toBe(1)
      await settings.locator('[data-setting="reduced-motion"] input').click()
      await settings.locator('[data-setting="fullscreen"] input').click()
      await settings.locator('[data-setting="text-size"] select').selectOption('large')
      await page.evaluate(() => window.__authoritativeRuntimeFixture.settle())
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().settings))
        .toEqual({ reducedMotion: true, fullscreen: false, textSize: 'large' })
      expect(await page.locator('.curse-production-environment').getAttribute('data-text-size'))
        .toBe('large')
      await page.keyboard.press('Escape')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        transient: { kind: 'pause', presentation: 'menu' }, proofInstance: instance,
      })
      await page.locator('.curse-pause-menu button', { hasText: 'Resume' }).click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        transient: null, proofInstance: instance,
      })
    } finally { await page.close() }
  })

  it('uses Registrar folio as the sole pause and settings treatment', async () => {
    const page = await openFixture()
    try {
      await page.keyboard.press('Escape')
      const presentation = page.locator('.curse-game-presentation')
      const menu = page.locator('.curse-pause-menu')
      const style = await menu.evaluate((node) => {
        const computed = getComputedStyle(node)
        return {
          color: computed.color,
          borderRadius: computed.borderRadius,
          transform: computed.transform,
        }
      })
      expect(await presentation.getAttribute('data-pause-candidate')).toBeNull()
      expect(style.color).toBe('rgb(48, 43, 35)')
      expect(style.borderRadius).toBe('1.28px')
      expect(style.transform).not.toBe('none')
      expect(await menu.locator('button').allTextContents()).toEqual([
        'Resume', 'Level selection', 'Settings', 'Exit game',
      ])
      await menu.locator('button', { hasText: 'Settings' }).click()
      expect(await page.locator('.curse-pause-settings [data-setting]').count()).toBe(3)
    } finally { await page.close() }
  })

  it('disposes the environment, views, global input, and native exit subscription exactly once', async () => {
    const page = await openFixture()
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      const writes = await page.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.dispose()
        fixture.dispose()
        fixture.nativeExit()
        window.dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape' }))
      })
      expect(await page.locator('.curse-production-environment').count()).toBe(0)
      expect(await page.locator('.curse-game-proof-canvas').count()).toBe(0)
      expect(await page.evaluate(() => ({
        unsubscribed: window.__authoritativeRuntimeFixture.unsubscribed(),
        writes: window.__authoritativeRuntimeFixture.writes().length,
        exits: window.__authoritativeRuntimeFixture.exits().length,
      }))).toEqual({ unsubscribed: true, writes, exits: 0 })
    } finally { await page.close() }
  })

  it('keeps a locked opening record resisted with no navigation or save', async () => {
    const page = await openFixture('opening')
    try {
      const observeResistance = async (selector: string): Promise<void> => page.evaluate((targetSelector) => {
        delete document.documentElement.dataset.observedRestriction
        const target = document.querySelector(targetSelector)
        if (!(target instanceof HTMLElement)) throw new Error(`resistance target missing: ${targetSelector}`)
        const observer = new MutationObserver(() => {
          if (!target.classList.contains('is-restriction-target')) return
          document.documentElement.dataset.observedRestriction = document
            .querySelector<HTMLElement>('.curse-folio')?.dataset.motionRestrictionKind ?? 'missing'
          observer.disconnect()
        })
        observer.observe(target, { attributes: true, attributeFilter: ['class'] })
      }, selector)
      const locked = page.locator('[data-status="locked"]').first()
      await observeResistance('[data-status="locked"]')
      await locked.click()
      await page.waitForFunction(() => document.documentElement.dataset.observedRestriction === 'refuse')
      const lockedCulture = page.locator('.curse-folio-culture-tab[aria-disabled="true"]').first()
      await observeResistance('.curse-folio-culture-tab[aria-disabled="true"]')
      await lockedCulture.focus()
      await page.keyboard.press('Enter')
      await page.waitForFunction(() => document.documentElement.dataset.observedRestriction === 'refuse')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        mode: 'archive', activePuzzle: null,
      })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes())).toEqual([])
    } finally { await page.close() }
  })

  it('presents optional authored pages without dialog, acknowledgement, or automatic focus', async () => {
    const page = await openFixture('opening')
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      const guidance = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().guidance)
      expect(guidance).toMatchObject({
        identity: { puzzle: first, intervention: 'opening-paired-veils' },
        page: 0,
      })
      const note = page.locator('.curse-guidance-note')
      expect(await note.count()).toBe(1)
      expect(await note.getAttribute('role')).toBeNull()
      expect(await note.locator('p').count()).toBe(1)
      expect(await note.locator('p').textContent()).toBe((guidance as any).intervention.pages[0])
      expect(await note.locator('button').allTextContents()).toEqual(['Next'])
      expect(await page.locator('[role="dialog"]').count()).toBe(0)
      expect(await note.evaluate((node) => node.contains(document.activeElement))).toBe(false)
      expect(await page.locator('.curse-game-proof-canvas').count()).toBe(1)

      for (let expectedPage = 1; expectedPage < 4; expectedPage += 1) {
        await note.locator('button').click()
        expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().guidance?.page))
          .toBe(expectedPage)
        expect(await note.locator('p').count()).toBe(1)
      }
      expect(await note.locator('button').count()).toBe(0)
      expect(await note.locator('p').textContent()).toMatch(/Eliminate the double cut.*Delete.*Backspace/)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.settle())
      expect(await page.evaluate(() => (window.__authoritativeRuntimeFixture.writes().at(-1) as any)
        .guidance.page)).toBe(3)
    } finally { await page.close() }
  })

  it('keeps large-text guidance in the passive edge rail clear of proof, timeline, and drawer', async () => {
    const page = await openFixture('opening')
    try {
      await page.setViewportSize({ width: 760, height: 900 })
      await page.evaluate(() => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'setTextSize', value: 'large' }))
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.evaluate((puzzle) => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'selectPuzzle', puzzle }), first)
      const intersections = await page.evaluate(() => {
        const rectangle = (selector: string): DOMRect => {
          const node = document.querySelector<HTMLElement>(selector)
          if (node === null) throw new Error(`guidance geometry node missing: ${selector}`)
          return node.getBoundingClientRect()
        }
        const note = rectangle('.curse-guidance-note')
        const overlaps = (other: DOMRect): boolean => note.left < other.right
          && note.right > other.left
          && note.top < other.bottom
          && note.bottom > other.top
        return {
          proof: overlaps(rectangle('.curse-production-aperture')),
          timeline: overlaps(rectangle('.curse-production-timeline-control')),
          drawer: overlaps(rectangle('.curse-production-folio-drawer-toggle')),
          fullyVisible: note.left >= 0 && note.top >= 0
            && note.right <= innerWidth && note.bottom <= innerHeight,
        }
      })
      expect(intersections).toEqual({
        proof: false,
        timeline: false,
        drawer: false,
        fullyVisible: true,
      })
    } finally { await page.close() }
  })

  it('uses the selected smoked-dark guidance treatment as the sole presentation', async () => {
    const page = await openFixture('opening')
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.evaluate((puzzle) => window.__authoritativeRuntimeFixture
        .dispatch({ kind: 'selectPuzzle', puzzle }), first)
      const presentation = page.locator('.curse-game-presentation')
      const style = await page.locator('.curse-guidance-note').evaluate((note) => {
        const computed = getComputedStyle(note)
        return {
          backgroundImage: computed.backgroundImage,
          color: computed.color,
          borderRightColor: computed.borderRightColor,
        }
      })
      expect(await presentation.getAttribute('data-guidance-candidate')).toBeNull()
      expect(style.backgroundImage).toContain('radial-gradient')
      expect(style.color).toBe('rgb(191, 232, 225)')
      expect(style.borderRightColor).toBe('rgb(98, 199, 191)')
    } finally { await page.close() }
  })

  it('keeps proof selection and Escape-to-pause live and allows solving from an unread page', async () => {
    const page = await openFixture('opening')
    try {
      const first = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${first}"]`).click()
      const rim = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofRegions.find((region: any) => region.kind === 'cut')!.rimClient)
      await page.mouse.move(rim.x, rim.y)
      await page.mouse.click(rim.x, rim.y)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().selection.length))
        .toBeGreaterThan(0)
      await page.mouse.click(rim.x, rim.y)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().selection))
        .toEqual([])

      await page.locator('.curse-game-proof-canvas').focus()
      await page.keyboard.press('Escape')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state())).toMatchObject({
        transient: { kind: 'pause', presentation: 'menu' },
        guidance: { page: 0 },
      })
      await page.getByRole('button', { name: 'Resume' }).click()
      await page.evaluate(() => window.__authoritativeRuntimeFixture.witness(0))
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('completion')
      expect(await page.locator('.curse-guidance-note').count()).toBe(0)
    } finally { await page.close() }
  })

  it('presents only authored nonblocking commentary for a recognized unwinnable state', async () => {
    const page = await openFixture('opening')
    try {
      const puzzles = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles())
      for (const puzzle of puzzles.slice(0, 2)) {
        await page.locator(`[data-puzzle="${puzzle}"]`).click()
        const count = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().steps.length)
        const witnessCount = puzzle === puzzles[0] ? 1 : 2
        expect(count).toBe(0)
        for (let index = 0; index < witnessCount; index++) {
          await page.evaluate((step) => window.__authoritativeRuntimeFixture.witness(step), index)
        }
        expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
          .toBe('completion')
        await page.locator('.curse-completion button').click()
      }

      await page.locator(`[data-puzzle="${puzzles[2]}"]`).click()
      await page.evaluate(() => window.__authoritativeRuntimeFixture.unwinnable())
      const guidance = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().guidance)
      expect(guidance).toMatchObject({
        identity: { puzzle: puzzles[2], intervention: 'empty-veil-trap' },
        page: 0,
      })
      const commentary = page.locator('.curse-guidance-note')
      expect(await commentary.count()).toBe(1)
      expect(await commentary.getAttribute('role')).toBeNull()
      expect(await commentary.locator('p').textContent()).toBe(
        'An empty veil is a familiar novice’s trap. Nothing remains inside it to work upon. Draw the lever back to before the clearing.',
      )
      expect(await page.locator('.curse-game-proof-canvas').count()).toBe(1)
      await page.locator('.curse-production-timeline-control').focus()
      await page.keyboard.press('Home')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(0)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().guidance))
        .toBeNull()
      expect(await commentary.count()).toBe(0)
    } finally { await page.close() }
  })

  it('keeps the actual scrolling sheet alive and restores each culture scroll after switching', async () => {
    const page = await openFixture('long')
    try {
      const firstSheet = await page.locator('.record-grid').elementHandle()
      if (firstSheet === null) throw new Error('first culture sheet missing')
      await firstSheet.evaluate((sheet) => {
        sheet.scrollTop = 90
        sheet.dispatchEvent(new Event('scroll'))
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.state().selectedScroll === 90)
      expect(await firstSheet.evaluate((sheet) => ({
        connected: sheet.isConnected, scrollTop: sheet.scrollTop,
      }))).toEqual({ connected: true, scrollTop: 90 })

      await page.locator('.curse-folio-culture-tab').nth(1).click()
      const secondSheet = page.locator('.record-grid')
      await secondSheet.evaluate((sheet) => {
        sheet.scrollTop = 55
        sheet.dispatchEvent(new Event('scroll'))
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.state().selectedScroll === 55)
      await page.locator('.curse-folio-culture-tab').nth(0).click()
      expect(await page.locator('.record-grid').evaluate((sheet) => sheet.scrollTop)).toBe(90)
      await page.locator('.curse-folio-culture-tab').nth(1).click()
      expect(await page.locator('.record-grid').evaluate((sheet) => sheet.scrollTop)).toBe(55)
    } finally { await page.close() }
  })

  it('routes live folio theorem drags through ordinary manifestation and refusal without false saves', async () => {
    const page = await openFixture('artifact')
    try {
      const [artifact, manifest] = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles())
      await page.locator(`[data-puzzle="${artifact}"]`).click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await page.locator(`[data-puzzle="${manifest}"]`).click()
      const target = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofRegions.find((region) => region.kind === 'cut' && region.polarity === 'negative')
        ?.interiorClient ?? null)
      if (target === null) throw new Error('manifestation host has no rendered negative field')
      const record = page.locator(`[data-puzzle="${artifact}"]`)
      const box = await record.boundingBox()
      if (box === null) throw new Error('completed artifact record is not rendered')
      const beforeManifest = await page.evaluate(() => window.__authoritativeRuntimeFixture.state())
      await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2)
      await page.mouse.down()
      await page.mouse.move(target.x, target.y)
      const lifted = await page.locator('.inspection-positioner.is-theorem-lifted').boundingBox()
      if (lifted === null) throw new Error('lifted theorem record has no presentation bounds')
      expect(lifted.x + lifted.width / 2).toBeCloseTo(target.x, 0)
      expect(lifted.y + lifted.height / 2).toBeCloseTo(target.y, 0)
      await page.mouse.up()
      expect(await page.locator('.curse-folio').getAttribute('data-motion-record-kind'))
        .toBe('return')
      expect(await page.evaluate(({ manifest }) => {
        const fixture = window.__authoritativeRuntimeFixture
        const save = fixture.writes().at(-1) as any
        return {
          state: fixture.state(),
          savedStep: save.attempts[manifest].steps.at(-1),
        }
      }, { manifest: manifest! })).toMatchObject({
        state: {
          mode: 'puzzle', cursor: 1, steps: ['theorem'],
          proofInstance: beforeManifest.proofInstance,
        },
        savedStep: { rule: 'theorem', direction: 'forward' },
      })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().proofRebuilds))
        .toBeGreaterThan(beforeManifest.proofRebuilds!)
      await page.waitForFunction((puzzle) => {
        const source = document.querySelector<HTMLElement>(`[data-puzzle="${puzzle}"]`)
        return source !== null && !source.classList.contains('is-inspection-source')
      }, artifact)

      const before = await page.evaluate(() => ({
        cursor: window.__authoritativeRuntimeFixture.state().cursor,
        writes: window.__authoritativeRuntimeFixture.writes().length,
      }))
      const replacement = page.locator(`[data-puzzle="${artifact}"]`)
      const replacementBox = await replacement.boundingBox()
      if (replacementBox === null) throw new Error('completed artifact replacement is not rendered')
      await page.mouse.move(
        replacementBox.x + replacementBox.width / 2,
        replacementBox.y + replacementBox.height / 2,
      )
      await page.mouse.down()
      await page.mouse.move(8, 8)
      await page.mouse.up()
      expect(await page.locator('.curse-refusal').count()).toBe(1)
      expect(await page.locator('.curse-refusal').textContent()).toMatch(/outside the active seal/)
      expect(await replacement.getAttribute('class')).not.toContain('is-theorem-lifted')
      expect(await page.evaluate(() => ({
        cursor: window.__authoritativeRuntimeFixture.state().cursor,
        writes: window.__authoritativeRuntimeFixture.writes().length,
      }))).toEqual(before)
    } finally { await page.close() }
  })

  it('routes a live folio theorem drag through ordinary exact dissolution', async () => {
    const page = await openFixture('artifact')
    try {
      const [artifact, , dissolve] = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles())
      await page.locator(`[data-puzzle="${artifact}"]`).click()
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await page.locator(`[data-puzzle="${dissolve}"]`).click()
      const target = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofRegions.find((region) => region.kind === 'bubble')?.client ?? null)
      if (target === null) throw new Error('dissolution host has no rendered theorem footprint')
      const record = page.locator(`[data-puzzle="${artifact}"]`)
      const box = await record.boundingBox()
      if (box === null) throw new Error('completed artifact record is not rendered')
      await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2)
      await page.mouse.down()
      await page.mouse.move(target.x, target.y)
      await page.mouse.up()
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.activeRafs() === 0)
      const completion = page.locator('.curse-completion')
      expect(await completion.count()).toBe(1)
      expect(await completion.locator('[data-completion-line]').textContent())
        .toBe('Restoration complete')
      expect(await completion.locator('h1').textContent()).toBe('Dissolve host')
      expect(await completion.locator('[data-completion-moves]').textContent()).toBe('1 move')
      expect(await completion.locator('[data-completion-response]').textContent()).not.toBe('')
      expect(await completion.locator('button').count()).toBe(1)
      expect(await completion.locator('button').textContent()).toBe('Return to level selection')
      expect(await page.locator('.curse-production-lens').count()).toBe(1)
      expect(await page.locator('.curse-production-timeline-housing').count()).toBe(1)
      expect(await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        const save = fixture.writes().at(-1) as any
        return {
          state: fixture.state(),
          save: {
            mode: save.mode,
            receipt: save.completionReceipt,
            hasAttempt: Object.hasOwn(save.attempts, save.activePuzzle),
          },
          activeRafs: fixture.activeRafs(),
        }
      })).toMatchObject({
        state: {
          mode: 'completion', activePuzzle: dissolve,
          hasProof: false, hasTimeline: false,
        },
        save: {
          mode: 'completion', receipt: { puzzle: dissolve, moves: 1, replay: false },
          hasAttempt: false,
        },
        activeRafs: 0,
      })
      await completion.locator('button').click()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().mode))
        .toBe('archive')
      expect(await page.locator('.curse-folio').count()).toBe(1)
      expect(await page.locator('.curse-completion').count()).toBe(0)
    } finally { await page.close() }
  })

  it('opens the actual editor, keeps host connection input live, owns local shortcuts, and closes before pause', async () => {
    const page = await openFixture('editor')
    try {
      const puzzle = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${puzzle}"]`).click()
      const bubble = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofRegions.find((region) => region.kind === 'bubble')?.rimClient ?? null)
      if (bubble === null) throw new Error('editor fixture has no rendered bubble')
      await page.mouse.click(bubble.x, bubble.y)
      await page.mouse.click(bubble.x, bubble.y, { button: 'right' })
      await page.waitForSelector('.curse-proof-menu')
      expect(await page.locator('.curse-proof-menu').textContent()).toContain('Construct a new relation')
      await page.getByRole('button', { name: 'Construct a new relation…' }).click()
      await page.waitForSelector('.cursebreaker-construction-loupe')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toEqual({ kind: 'editor' })
      const loupe = page.locator('.cursebreaker-construction-loupe')
      const loupeBox = await loupe.boundingBox()
      if (loupeBox === null) throw new Error('the construction loupe has no rendered bounds')
      const moveX = loupeBox.x + loupeBox.width / 2 < 700 ? 800 : -800
      await page.mouse.move(loupeBox.x + loupeBox.width * .995, loupeBox.y + loupeBox.height / 2)
      await page.mouse.down()
      await page.mouse.move(
        loupeBox.x + loupeBox.width * .995 + moveX,
        loupeBox.y + loupeBox.height / 2,
      )
      await page.mouse.up()
      const hostWire = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .construction?.hostWires.find((wire) => wire.point !== null)?.point ?? null)
      if (hostWire === null) {
        const construction = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().construction)
        throw new Error(`the real construction puzzle has no rendered host wire: ${JSON.stringify(construction)}`)
      }
      await page.mouse.move(hostWire.x, hostWire.y)
      await page.mouse.down()
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .construction?.connection?.source.kind)).toBe('host')
      await page.mouse.up()
      const cursor = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)
      await page.keyboard.press('Control+Z')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(cursor)
      await page.evaluate(() => window.__authoritativeRuntimeFixture.dispatch({ kind: 'setReducedMotion', value: true }))
      expect(await page.locator('.cursebreaker-construction-loupe').getAttribute('class')).toContain('is-reduced-motion')
      await page.keyboard.press('Escape')
      await page.waitForSelector('.cursebreaker-construction-loupe', { state: 'detached' })
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toBeNull()
    } finally { await page.close() }
  })

  it('lets Escape pause during active proof motion while default-prevented Ctrl-Z cannot rewind beneath it', async () => {
    const openMoving = async (): Promise<Page> => {
      const page = await openFixture('motion')
      const puzzle = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${puzzle}"]`).click()
      await page.evaluate(() => window.__authoritativeRuntimeFixture.witness(0))
      const term = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofNodes.find((node) => node.kind === 'term')?.client ?? null)
      if (term === null) throw new Error('motion fixture has no rendered term')
      await page.mouse.dblclick(term.x, term.y)
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.state().motionPlaying)
      return page
    }

    const dispatchKeyDuringMotion = async (page: Page, key: string): Promise<void> => {
      await page.evaluate((pressed) => {
        const fixture = window.__authoritativeRuntimeFixture
        if (!fixture.state().motionPlaying) throw new Error('proof motion ended before key dispatch')
        const canvas = document.querySelector('.curse-game-proof-canvas')
        if (!(canvas instanceof HTMLCanvasElement)) throw new Error('proof canvas missing')
        canvas.dispatchEvent(new KeyboardEvent('keydown', {
          key: pressed,
          ctrlKey: pressed.toLowerCase() === 'z',
          bubbles: true,
          cancelable: true,
        }))
      }, key)
    }

    const escapePage = await openMoving()
    try {
      await dispatchKeyDuringMotion(escapePage, 'Escape')
      expect(await escapePage.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toEqual({
        kind: 'pause', presentation: 'menu',
      })
    } finally { await escapePage.close() }

    const rewindPage = await openMoving()
    try {
      await dispatchKeyDuringMotion(rewindPage, 'z')
      expect(await rewindPage.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)
    } finally { await rewindPage.close() }

    const timelinePage = await openMoving()
    try {
      await timelinePage.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        if (!fixture.state().motionPlaying) throw new Error('proof motion ended before timeline key dispatch')
        const control = document.querySelector('.curse-production-timeline-control')
        if (!(control instanceof HTMLElement)) throw new Error('timeline control missing')
        control.dispatchEvent(new KeyboardEvent('keydown', {
          key: 'Home', bubbles: true, cancelable: true,
        }))
      })
      expect(await timelinePage.evaluate(() => window.__authoritativeRuntimeFixture.state().cursor)).toBe(1)
    } finally { await timelinePage.close() }

    const exitPage = await openMoving()
    try {
      await exitPage.evaluate(() => window.__authoritativeRuntimeFixture.nativeExit())
      await exitPage.waitForFunction(() => window.__authoritativeRuntimeFixture.exits().length === 1)
      const writes = await exitPage.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)
      await exitPage.waitForFunction(() => !window.__authoritativeRuntimeFixture.state().motionPlaying)
      expect(await exitPage.evaluate(() => ({
        cursor: window.__authoritativeRuntimeFixture.state().cursor,
        writes: window.__authoritativeRuntimeFixture.writes().length,
      }))).toEqual({ cursor: 1, writes })
    } finally { await exitPage.close() }
  })

  it('cancels an in-flight proof gesture when pause takes input ownership', async () => {
    const page = await openFixture('motion')
    try {
      const puzzle = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${puzzle}"]`).click()
      await page.evaluate(() => window.__authoritativeRuntimeFixture.witness(0))
      await page.waitForFunction(() => !window.__authoritativeRuntimeFixture.state().motionPlaying)
      const before = await page.evaluate(() => window.__authoritativeRuntimeFixture.state()
        .proofNodes.find((node) => node.kind === 'term')?.client ?? null)
      if (before === null) throw new Error('gesture fixture has no rendered term')
      await page.keyboard.down('Control')
      await page.mouse.move(before.x, before.y)
      await page.mouse.down()
      expect(await page.locator('.curse-game-proof-canvas').evaluate((canvas) =>
        (canvas as HTMLCanvasElement).hasPointerCapture(1))).toBe(true)
      await page.keyboard.press('Escape')
      expect(await page.locator('.curse-game-proof-canvas').evaluate((canvas) =>
        (canvas as HTMLCanvasElement).hasPointerCapture(1))).toBe(false)
      const release = await page.evaluate(({ x, y }) => {
        const fixture = window.__authoritativeRuntimeFixture
        const canvas = document.querySelector('.curse-game-proof-canvas')
        if (!(canvas instanceof HTMLCanvasElement)) throw new Error('proof canvas missing')
        const position = () => fixture.state()
          .proofNodes.find((node) => node.kind === 'term')?.client ?? null
        const beforeRelease = position()
        canvas.dispatchEvent(new PointerEvent('pointermove', {
          pointerId: 1, clientX: x, clientY: y, ctrlKey: true, bubbles: true,
        }))
        canvas.dispatchEvent(new PointerEvent('pointerup', {
          pointerId: 1, clientX: x, clientY: y, ctrlKey: true, bubbles: true,
        }))
        return { beforeRelease, afterRelease: position() }
      }, { x: before.x + 55, y: before.y + 38 })
      expect(release.afterRelease).toEqual(release.beforeRelease)
      await page.mouse.move(before.x + 55, before.y + 38)
      await page.mouse.up()
      await page.keyboard.up('Control')
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.state().transient)).toEqual({
        kind: 'pause', presentation: 'menu',
      })
    } finally { await page.close() }
  })

  it('resizes the active proof backing canvas through the observed production slot', async () => {
    const page = await openFixture()
    try {
      const puzzle = await page.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await page.locator(`[data-puzzle="${puzzle}"]`).click()
      const before = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().canvas)
      await page.setViewportSize({ width: 760, height: 620 })
      await page.waitForFunction((width) => window.__authoritativeRuntimeFixture.state().canvas?.width !== width, before!.width)
      const after = await page.evaluate(() => window.__authoritativeRuntimeFixture.state().canvas)
      expect(after!.width).toBe(Math.round(after!.clientWidth))
      expect(after!.height).toBe(Math.round(after!.clientHeight))
      expect(after!.width).not.toBe(before!.width)
    } finally { await page.close() }
  })

  it('blocks folio navigation and theorem lift beneath pause ownership', async () => {
    const archive = await openFixture()
    try {
      const first = await archive.evaluate(() => window.__authoritativeRuntimeFixture.puzzles()[0]!)
      await archive.setViewportSize({ width: 760, height: 900 })
      const drawerToggle = archive.locator('.curse-production-folio-drawer-toggle')
      expect(await drawerToggle.getAttribute('aria-expanded')).toBe('false')
      await archive.keyboard.press('Escape')
      await drawerToggle.evaluate((toggle) => toggle.dispatchEvent(new MouseEvent('click', {
        bubbles: true,
        cancelable: true,
      })))
      expect(await drawerToggle.getAttribute('aria-expanded')).toBe('false')
      await archive.setViewportSize({ width: 1400, height: 900 })
      await archive.locator(`[data-puzzle="${first}"]`).evaluate((record) =>
        record.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true })))
      expect(await archive.evaluate(() => ({
        mode: window.__authoritativeRuntimeFixture.state().mode,
        writes: window.__authoritativeRuntimeFixture.writes().length,
      }))).toEqual({ mode: 'archive', writes: 1 })
    } finally { await archive.close() }

    const puzzle = await openFixture('artifact')
    try {
      const [artifact, manifest] = await puzzle.evaluate(() => window.__authoritativeRuntimeFixture.puzzles())
      await puzzle.locator(`[data-puzzle="${artifact}"]`).click()
      await puzzle.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.witness(0)
        fixture.dispatch({ kind: 'levelSelection' })
      })
      await puzzle.locator(`[data-puzzle="${manifest}"]`).click()
      await puzzle.keyboard.press('Escape')
      const writes = await puzzle.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)
      const record = puzzle.locator(`[data-puzzle="${artifact}"]`)
      const box = await record.boundingBox()
      if (box === null) throw new Error('completed artifact record is missing')
      await record.evaluate((source, { x, y }) => source.dispatchEvent(new PointerEvent(
        'pointerdown',
        { pointerId: 29, button: 0, clientX: x, clientY: y, bubbles: true, cancelable: true },
      )), { x: box.x + box.width / 2, y: box.y + box.height / 2 })
      expect(await record.getAttribute('class')).not.toContain('is-theorem-lifted')
      expect(await puzzle.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)).toBe(writes)
    } finally { await puzzle.close() }
  })

  it('uses saved reduced motion rather than the competing OS media preference', async () => {
    const page = await openFixture('null', 'reduce')
    try {
      await page.evaluate(() => window.__authoritativeRuntimeFixture.dispatch({ kind: 'setReducedMotion', value: false }))
      expect(await page.locator('.curse-production-folio-host').evaluate((node) => getComputedStyle(node).transitionDuration)).not.toBe('0s')
      await page.evaluate(() => window.__authoritativeRuntimeFixture.dispatch({ kind: 'setReducedMotion', value: true }))
      expect(await page.locator('.curse-production-folio-host').evaluate((node) => getComputedStyle(node).transitionDuration)).toBe('0s')
    } finally { await page.close() }
  })

  it('does not reconcile fullscreen after disposal while its platform effect is pending', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => {
        const fixture = window.__authoritativeRuntimeFixture
        fixture.setFullscreenResult(true)
        fixture.deferFullscreen()
        fixture.dispatch({ kind: 'setFullscreen', value: false })
      })
      await page.waitForFunction(() => window.__authoritativeRuntimeFixture.fullscreenRequests().length === 1)
      const writes = await page.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)
      await page.evaluate(() => {
        window.__authoritativeRuntimeFixture.dispose()
        window.__authoritativeRuntimeFixture.releaseFullscreen()
      })
      await page.waitForTimeout(0)
      expect(await page.evaluate(() => window.__authoritativeRuntimeFixture.writes().length)).toBe(writes)
    } finally { await page.close() }
  })
})
