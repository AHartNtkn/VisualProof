import { expect, test, type Page } from '@playwright/test'

type Point = { readonly x: number; readonly y: number }
type WirePoint = { readonly wire: string; readonly point: Point | null }

declare global {
  interface Window {
    __comprehensionDebug?: {
      open(): void
      addConstant(): void
      state(): {
        boundary: string[]
        formalBoundary: string[]
        externalWires: { draftWire: string; hostWire: string }[]
        proofSelected: { kind: string; id: string } | null
        referencePreview: {
          source: { kind: 'draft' | 'host'; wire: string }
          draftTargets: string[]
          hostTargets: string[]
          dragging: boolean
          activeTarget: { kind: 'draft' | 'host'; wire: string } | null
        } | null
      }
      fixture: { parameter: string }
      draftWires(): WirePoint[]
      hostWires(): WirePoint[]
    }
  }
}

const demoUrl = 'http://127.0.0.1:4174/ui-lab/round13-a.html?debug'

async function openDraft(page: Page): Promise<void> {
  await page.setViewportSize({ width: 1400, height: 900 })
  await page.goto(demoUrl)
  await page.waitForFunction(() => window.__comprehensionDebug !== undefined)
  await page.evaluate(() => window.__comprehensionDebug!.open())
  await expect(page.locator('.comp-editor')).toBeVisible()
  await page.waitForTimeout(400)
}

async function wirePoint(page: Page, side: 'host' | 'draft', wire: string): Promise<Point> {
  const point = await page.evaluate(({ side, wire }) => {
    const debug = window.__comprehensionDebug!
    const found = (side === 'host' ? debug.hostWires() : debug.draftWires()).find((value) => value.wire === wire)
    return found?.point ?? null
  }, { side, wire })
  expect(point, `${side} wire '${wire}' is rendered`).not.toBeNull()
  return point!
}

async function drag(page: Page, from: Point, to: Point): Promise<void> {
  await page.mouse.move(from.x, from.y)
  await page.mouse.down()
  await page.mouse.move(to.x, to.y, { steps: 8 })
  await page.mouse.up()
}

test('a proof wire draws into a formal editor port through the shared checked gesture', async ({ page }) => {
  await openDraft(page)
  const parameter = await page.evaluate(() => window.__comprehensionDebug!.fixture.parameter)
  const from = await wirePoint(page, 'host', parameter)
  const to = await wirePoint(page, 'draft', 'arg1')

  await page.mouse.move(from.x, from.y)
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().referencePreview)).toMatchObject({
    source: { kind: 'host', wire: parameter },
    draftTargets: expect.arrayContaining(['arg1']),
    hostTargets: [],
    dragging: false,
  })
  await page.mouse.down()
  await page.mouse.move((from.x + to.x) / 2, (from.y + to.y) / 2, { steps: 4 })
  await expect(page.locator('.comp-join-gesture')).toHaveCount(1)
  await page.mouse.move(to.x, to.y, { steps: 4 })
  await page.mouse.up()

  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state())).toMatchObject({
    boundary: ['arg1', 'arg2', 'arg1'],
    externalWires: [{ draftWire: 'arg1', hostWire: parameter }],
  })
  await expect(page.locator('.comp-join-gesture')).toHaveCount(0)
})

test('reusing one proof wire fuses a second formal port without spawning another import', async ({ page }) => {
  await openDraft(page)
  const parameter = await page.evaluate(() => window.__comprehensionDebug!.fixture.parameter)
  const host = await wirePoint(page, 'host', parameter)
  await drag(page, host, await wirePoint(page, 'draft', 'arg1'))

  await page.mouse.move(host.x, host.y)
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().referencePreview)).toMatchObject({
    source: { kind: 'host', wire: parameter },
    draftTargets: ['arg2'],
  })
  await drag(page, host, await wirePoint(page, 'draft', 'arg2'))
  await expect(page.locator('.comp-status')).toContainText('Lines joined — one individual now.')

  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state())).toMatchObject({
    formalBoundary: ['arg1', 'arg1'],
    boundary: ['arg1', 'arg1', 'arg1'],
    externalWires: [{ draftWire: 'arg1', hostWire: parameter }],
  })
  expect(await page.evaluate(() => window.__comprehensionDebug!.draftWires().some((wire) => wire.wire === 'arg2'))).toBe(false)

  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state())).toMatchObject({
    formalBoundary: ['arg1', 'arg2'],
    boundary: ['arg1', 'arg2', 'arg1'],
    externalWires: [{ draftWire: 'arg1', hostWire: parameter }],
  })
  await page.keyboard.press('Control+Shift+z')
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().boundary)).toEqual(['arg1', 'arg1', 'arg1'])
})

test('host-origin drawing reaches a formal-fused line and participates in ordinary draft history', async ({ page }) => {
  await openDraft(page)
  await page.evaluate(() => window.__comprehensionDebug!.addConstant())
  await page.waitForTimeout(300)

  const local = await wirePoint(page, 'draft', 'w')
  const arg2 = await wirePoint(page, 'draft', 'arg2')
  await drag(page, local, arg2)

  const parameter = await page.evaluate(() => window.__comprehensionDebug!.fixture.parameter)
  const host = await wirePoint(page, 'host', parameter)
  await page.mouse.move(host.x, host.y)
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().referencePreview)).toMatchObject({
    source: { kind: 'host', wire: parameter },
    draftTargets: expect.arrayContaining(['arg2']),
    dragging: false,
  })
  const attachedArg2 = await wirePoint(page, 'draft', 'arg2')
  await page.mouse.move(host.x, host.y)
  await page.mouse.down()
  await page.mouse.move(attachedArg2.x, attachedArg2.y, { steps: 8 })
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().referencePreview?.activeTarget)).toEqual({ kind: 'draft', wire: 'arg2' })
  await page.mouse.up()

  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().externalWires)).toEqual([
    { draftWire: 'arg2', hostWire: parameter },
  ])
  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().externalWires)).toEqual([])
  await page.keyboard.press('Control+Shift+z')
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().externalWires)).toEqual([
    { draftWire: 'arg2', hostWire: parameter },
  ])
})

test('host-to-host and cancelled host gestures mutate nothing while still-click selects', async ({ page }) => {
  await openDraft(page)
  const parameter = await page.evaluate(() => window.__comprehensionDebug!.fixture.parameter)
  const source = await wirePoint(page, 'host', parameter)

  await page.mouse.move(source.x, source.y)
  await page.mouse.down()
  await page.mouse.move(source.x - 24, source.y + 18, { steps: 4 })
  await page.mouse.move(source.x, source.y, { steps: 4 })
  await page.mouse.up()
  await expect(page.locator('.comp-status')).toContainText('host wires are read-only')
  expect(await page.evaluate(() => window.__comprehensionDebug!.state().externalWires)).toEqual([])

  const formal = await wirePoint(page, 'draft', 'arg1')
  await page.mouse.move(source.x, source.y)
  await page.mouse.down()
  await page.mouse.move((source.x + formal.x) / 2, (source.y + formal.y) / 2, { steps: 4 })
  await page.locator('.proof-canvas').dispatchEvent('pointercancel', { pointerId: 1 })
  await page.mouse.up()
  await expect(page.locator('.comp-join-gesture')).toHaveCount(0)
  expect(await page.evaluate(() => window.__comprehensionDebug!.state().externalWires)).toEqual([])

  await page.mouse.click(source.x, source.y)
  await expect.poll(() => page.evaluate(() => window.__comprehensionDebug!.state().proofSelected)).toEqual({ kind: 'wire', id: parameter })
})
