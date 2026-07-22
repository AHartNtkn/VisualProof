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
  const page = await browser.newPage({ viewport: { width: 1600, height: 900 } })
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

  it('keeps keyboard focus without a rectangular canvas border beneath the gasket', async () => {
    const page = await openFixture()
    try {
      const canvas = page.locator('.curse-game-proof-canvas')
      await canvas.focus()
      const style = await canvas.evaluate((node) => {
        const computed = getComputedStyle(node)
        return {
          borderTopWidth: computed.borderTopWidth,
          outlineStyle: computed.outlineStyle,
          outlineWidth: computed.outlineWidth,
        }
      })
      expect(style).toEqual({
        borderTopWidth: '0px',
        outlineStyle: 'none',
        outlineWidth: '0px',
      })
      expect(await canvas.evaluate((node) => node === document.activeElement)).toBe(true)
    } finally { await page.close() }
  })

  it('uses the proof-action palette for the construction context menu', async () => {
    const page = await openFixture()
    try {
      const proofPoint = await page.evaluate(() => window.__gameProofSurfaceFixture.proofNodePoint())
      await page.mouse.click(proofPoint.x, proofPoint.y, { button: 'right' })
      const proofMenu = page.locator('.curse-context-menu--proof')
      await expect.poll(() => proofMenu.count()).toBe(1)
      const proofPalette = await proofMenu.evaluate((node) => {
        const style = getComputedStyle(node)
        return {
          backgroundColor: style.backgroundColor,
          borderTopColor: style.borderTopColor,
          color: style.color,
          boxShadow: style.boxShadow,
        }
      })

      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.open())).toBe(true)
      await page.locator('.cursebreaker-construction-loupe__canvas')
        .click({ button: 'right', position: { x: 210, y: 210 } })
      const constructionMenu = page.locator('.vpa-spawn-column')
      await expect.poll(() => constructionMenu.count()).toBe(1)
      const constructionPalette = await constructionMenu.evaluate((node) => {
        const style = getComputedStyle(node)
        return {
          backgroundColor: style.backgroundColor,
          borderTopColor: style.borderTopColor,
          color: style.color,
          boxShadow: style.boxShadow,
        }
      })
      expect(constructionPalette).toEqual(proofPalette)
    } finally { await page.close() }
  })

  it('uses plain pointer input only to select and Shift pointer input only to deselect', async () => {
    const page = await openFixture()
    try {
      const points = await page.evaluate(() => window.__gameProofSurfaceFixture.proofNodePoints())
      expect(points).toHaveLength(2)
      const [first, second] = points as [typeof points[number], typeof points[number]]

      await page.mouse.click(first.x, first.y)
      const once = await page.evaluate(() => window.__gameProofSurfaceFixture.selection())
      expect(once).toHaveLength(1)
      await page.mouse.click(first.x, first.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual(once)

      await page.keyboard.down('Shift')
      await page.mouse.click(first.x, first.y)
      await page.keyboard.up('Shift')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])

      await page.keyboard.down('Shift')
      await page.mouse.click(first.x, first.y)
      await page.keyboard.up('Shift')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])

      await page.mouse.click(first.x, first.y)
      await page.mouse.click(second.x, second.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toHaveLength(2)
      const proofMoves = await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())
      await page.keyboard.down('Shift')
      await page.mouse.move(first.x, first.y)
      await page.mouse.down()
      await page.mouse.move(second.x, second.y, { steps: 12 })
      await page.mouse.up()
      await page.keyboard.up('Shift')
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.prepared())).toBe(proofMoves)

      const canvas = await page.locator('.curse-game-proof-canvas').boundingBox()
      if (canvas === null) throw new Error('proof canvas missing')
      await page.mouse.click(first.x, first.y)
      await page.mouse.click(canvas.x + 4, canvas.y + 4)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])
    } finally { await page.close() }
  })

  it('iterates an already-selected cut together with its nested contents', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => window.__gameProofSurfaceFixture.freezeLayout())
      const gesture = await page.evaluate(() =>
        window.__gameProofSurfaceFixture.cutIterationGesture())
      await page.evaluate(() => window.__gameProofSurfaceFixture.selectIterationCut())
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection()))
        .toEqual([`region:${gesture.cut}`])

      const before = await page.evaluate(() => window.__gameProofSurfaceFixture.iterationSnapshot())
      await page.mouse.move(gesture.start.x, gesture.start.y)
      await page.mouse.down()
      await page.mouse.move(gesture.target.x, gesture.target.y, { steps: 12 })
      await page.mouse.up()
      await page.waitForFunction((prepared) =>
        window.__gameProofSurfaceFixture.iterationSnapshot().prepared > prepared, before.prepared)
      const after = await page.evaluate(() => window.__gameProofSurfaceFixture.iterationSnapshot())

      expect(after.lastStep).toMatchObject({
        rule: 'iteration',
        sel: { region: gesture.root, regions: [gesture.cut], nodes: [], wires: [] },
        target: gesture.root,
      })
      expect(after.cutCopies).toBe(before.cutCopies + 1)
      expect(after.regions).toBe(before.regions + 2)
      expect(after.nodes).toBe(before.nodes + 2)
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
      const hostPoints = await page.evaluate(() => {
        const proofCanvas = document.querySelector('.curse-game-proof-canvas')
        return window.__gameProofSurfaceFixture.construction()!.hostWires
          .filter((wire) => wire.point !== null
            && document.elementFromPoint(wire.point.x, wire.point.y) === proofCanvas)
          .map((wire) => ({ wire: wire.wire, point: wire.point! }))
      })
      let hostPoint: { x: number; y: number } | null = null
      const observed: unknown[] = []
      for (const candidate of hostPoints) {
        await page.mouse.move(candidate.point.x, candidate.point.y)
        const connection = await page.evaluate(() =>
          window.__gameProofSurfaceFixture.construction()!.connection)
        observed.push({ candidate, connection })
        if ((connection?.draftTargets.length ?? 0) > 0) { hostPoint = candidate.point; break }
      }
      if (hostPoint === null) throw new Error(`no host line has a pointer-reachable compatible draft target: ${JSON.stringify(observed)}`)
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

  it('selects and imports an enclosing nullary binder through the live proof viewport', async () => {
    const page = await openFixture()
    try {
      await page.evaluate(() => window.__gameProofSurfaceFixture.freezeLayout())
      const target = await page.evaluate(() => ({
        id: window.__gameProofSurfaceFixture.dependentBubble(),
        point: window.__gameProofSurfaceFixture.dependentBubblePoint(),
      }))
      await page.mouse.click(target.point.x, target.point.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection()))
        .toEqual([`region:${target.id}`])

      await page.mouse.click(target.point.x, target.point.y, { button: 'right' })
      await page.getByRole('button', { name: 'Construct a new relation…' }).click()
      await page.waitForSelector('.cursebreaker-construction-loupe')

      const host = await page.evaluate(() => ({
        atom: window.__gameProofSurfaceFixture.hostAtom(),
        binder: window.__gameProofSurfaceFixture.expectedHostBinder(),
        point: window.__gameProofSurfaceFixture.hostAtomPoint(),
        voidPoint: window.__gameProofSurfaceFixture.voidPoint(),
      }))
      const proofCanvas = page.locator('.curse-game-proof-canvas')
      const hostReachable = async (): Promise<boolean> => page.evaluate(
        ({ x, y }) => document.elementFromPoint(x, y)?.classList.contains('curse-game-proof-canvas') ?? false,
        host.point,
      )
      if (!await hostReachable()) {
        const loupe = page.locator('.cursebreaker-construction-loupe')
        const box = await loupe.boundingBox()
        if (box === null) throw new Error('construction loupe has no rendered box')
        const start = { x: box.x + box.width * .995, y: box.y + box.height / 2 }
        const destination = {
          x: host.point.x < 800 ? 1320 : 280,
          y: host.point.y < 450 ? 700 : 200,
        }
        await page.mouse.move(start.x, start.y)
        await page.mouse.down()
        await page.mouse.move(
          start.x + destination.x - (box.x + box.width / 2),
          start.y + destination.y - (box.y + box.height / 2),
          { steps: 12 },
        )
        await page.mouse.up()
      }
      expect(await hostReachable()).toBe(true)

      await page.mouse.click(host.voidPoint.x, host.voidPoint.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection())).toEqual([])
      await page.mouse.click(host.point.x, host.point.y)
      expect(await page.evaluate(() => window.__gameProofSurfaceFixture.selection()))
        .toEqual([`node:${host.atom}`])

      const loupeCanvas = page.locator('.cursebreaker-construction-loupe__canvas')
      const destination = await loupeCanvas.boundingBox()
      if (destination === null) throw new Error('construction loupe canvas has no rendered box')
      await page.mouse.move(host.point.x, host.point.y)
      await page.mouse.down()
      await page.mouse.move(
        destination.x + destination.width / 2,
        destination.y + destination.height / 2,
        { steps: 12 },
      )
      await page.mouse.up()

      const imported = await page.evaluate(() => window.__gameProofSurfaceFixture.construction()!.binders)
      expect(imported).toHaveLength(1)
      expect(imported[0]![1]).toBe(host.binder)

      await loupeCanvas.focus()
      await page.keyboard.press('Enter')
      await page.waitForSelector('.cursebreaker-construction-loupe', { state: 'detached' })
      const step = await page.evaluate(() => window.__gameProofSurfaceFixture.lastPreparedStep())
      expect(step).toMatchObject({
        rule: 'comprehensionInstantiate',
        bubble: target.id,
        binders: [[imported[0]![0], host.binder]],
      })
      expect(await proofCanvas.count()).toBe(1)
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
        const rail = await slider.boundingBox()
        if (rail === null) throw new Error('timeline slider has no rendered box')
        await page.mouse.click(center.x, rail.y + rail.height / 2)
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
