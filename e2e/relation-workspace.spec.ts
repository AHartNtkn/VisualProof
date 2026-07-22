import { expect, test, type Page } from '@playwright/test'

type FixtureState = {
  cancelCount: number
  finalizeCount: number
  refusals: string[]
  debug: null | {
    mode: 'substitute' | 'abstract'
    cursor: number
    historyLength: number
    rect: { left: number; top: number; width: number; height: number }
    materializedBoundary: string[]
    status: { kind: 'ready' | 'refused'; code: string; message: string }
    transaction: null | {
      candidateCount: number
      activeIndex: number
      activeKeys: string[]
      excludedKeys: string[]
    }
    draftBodies: { node: string; kind: string; point: { x: number; y: number } }[]
    draftWires: { wire: string; point: { x: number; y: number } | null }[]
  }
}

declare global {
  interface Window {
    relationWorkspaceFixture: {
      mount(mode: 'substitute' | 'abstract', finalizeBehavior?: 'succeed' | 'refuse'): void
      mountAbstractionScenario(scenario: 'multi-set' | 'zero-match' | 'matcher-exhausted' | 'solver-exhausted' | 'stale-source' | 'kernel-refusal' | 'invalid-ports'): void
      setTheme(mode: 'light' | 'dark'): void
      staleSource(): void
      state(): FixtureState
    }
  }
}

async function openFixture(page: Page): Promise<void> {
  await page.goto('/test/relation-workspace.html')
  await page.waitForFunction(() => window.relationWorkspaceFixture !== undefined)
}

async function state(page: Page): Promise<FixtureState> {
  return page.evaluate(() => window.relationWorkspaceFixture.state())
}

async function spawnWorkspaceTerm(page: Page, source: string, x: number): Promise<void> {
  const canvas = (await page.locator('.vpa-relation-canvas').boundingBox())!
  await page.mouse.click(canvas.x + canvas.width * x, canvas.y + canvas.height * 0.58, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill(source)
  await page.getByLabel('Lambda term to spawn').press('Enter')
  await page.waitForTimeout(350)
}

async function dropWireOnStrip(page: Page, wire: string, optionalOffset = 38): Promise<void> {
  const point = (await state(page)).debug!.draftWires.find((candidate) => candidate.wire === wire)!.point!
  const strip = (await page.locator('.vpa-relation-port-strip').boundingBox())!
  const target = { x: strip.x + strip.width - optionalOffset, y: strip.y + strip.height / 2 }
  expect(await page.evaluate(({ point, target }) => ({
    source: document.elementFromPoint(point.x, point.y)?.className,
    target: document.elementFromPoint(target.x, target.y)?.className,
  }), { point, target })).toEqual({ source: 'vpa-relation-canvas', target: 'vpa-relation-port-strip' })
  await page.mouse.move(point.x, point.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y, { steps: 8 })
  await page.mouse.up()
}

test('one mounted RelationWorkspace renders both transaction configurations and owns lifecycle', async ({ page }) => {
  await openFixture(page)
  for (const configured of [
    { mode: 'substitute' as const, title: 'SUBSTITUTE FIXTURE', finalize: 'Instantiate' },
    { mode: 'abstract' as const, title: 'ABSTRACT FIXTURE', finalize: 'Abstract' },
  ]) {
    await page.evaluate((mode) => window.relationWorkspaceFixture.mount(mode), configured.mode)
    const dialog = page.locator('.vpa-relation-workspace')
    await expect(dialog).toHaveCount(1)
    await expect(dialog).toHaveAttribute('aria-label', configured.title)
    await expect(dialog.getByRole('button', { name: configured.finalize, exact: true })).toBeVisible()
    await expect(dialog.locator('.vpa-relation-status')).toHaveText('ready')
    await expect(dialog.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'ready')
    expect((await state(page)).debug?.mode).toBe(configured.mode)
    const cursorBeforeUndo = (await state(page)).debug!.cursor
    await page.keyboard.press('Control+z')
    expect((await state(page)).debug?.cursor).toBe(cursorBeforeUndo - 1)
    await page.keyboard.press('Control+Shift+z')
    expect((await state(page)).debug?.cursor).toBe(cursorBeforeUndo)

    const beforeMove = (await state(page)).debug!.rect
    const title = (await page.locator('.vpa-relation-title').boundingBox())!
    await page.mouse.move(title.x + title.width * 0.35, title.y + title.height / 2)
    await page.mouse.down()
    await page.mouse.move(title.x + title.width * 0.35 + 30, title.y + title.height / 2 + 20)
    await page.mouse.up()
    expect((await state(page)).debug!.rect.left).toBeGreaterThan(beforeMove.left)

    const beforeResize = (await state(page)).debug!.rect
    const resize = (await page.locator('.vpa-relation-resize').boundingBox())!
    await page.mouse.move(resize.x + resize.width / 2, resize.y + resize.height / 2)
    await page.mouse.down()
    await page.mouse.move(resize.x + resize.width / 2 + 25, resize.y + resize.height / 2 + 15)
    await page.mouse.up()
    expect((await state(page)).debug!.rect.width).toBeGreaterThan(beforeResize.width)

    await dialog.getByRole('button', { name: 'Cancel', exact: true }).click()
    await expect(dialog).toHaveCount(0)
    expect((await state(page)).cancelCount).toBe(1)
  }

  await page.evaluate(() => window.relationWorkspaceFixture.mount('abstract', 'refuse'))
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  await expect(page.locator('.vpa-relation-status')).toHaveText('fixture kernel refusal')
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'kernel-refusal')
  expect(await state(page)).toMatchObject({ cancelCount: 0, finalizeCount: 0, refusals: ['fixture kernel refusal'] })
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  expect((await state(page)).cancelCount).toBe(1)

  await page.evaluate(() => window.relationWorkspaceFixture.mount('abstract', 'succeed'))
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  expect(await state(page)).toMatchObject({ cancelCount: 0, finalizeCount: 1, debug: null })
})

test('mounted boundary ports and the empty marker expose their editable state to keyboard users', async ({ page }) => {
  await openFixture(page)
  await page.evaluate(() => window.relationWorkspaceFixture.mount('substitute'))

  const strip = page.locator('.vpa-relation-port-strip')
  await expect(strip).toHaveAttribute('aria-label', 'Relation boundary ports')
  const forced = strip.locator('.vpa-relation-port.is-forced')
  const optional = strip.locator('.vpa-relation-port.is-optional')
  await expect(forced).toHaveAttribute('aria-label', 'Forced relation port 1, locked')
  await expect(optional).toHaveAttribute('aria-label', 'Optional relation port 2, unbound')
  await forced.focus()
  await expect(forced).toBeFocused()
  await optional.focus()
  await expect(optional).toBeFocused()

  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('stale-source'))
  const marker = page.locator('.vpa-relation-empty-marker')
  await expect(marker).toHaveCount(1)
  await expect(marker).toHaveAttribute('aria-pressed', 'true')
  await expect(marker).toHaveAttribute('aria-label', /Empty occurrence marker selected/)
  await marker.click()
  await expect(marker).toHaveAttribute('aria-pressed', 'false')
  await expect(page.locator('.vpa-relation-status')).toHaveText('ready for a trivial wrap')
  await marker.press('Enter')
  await expect(marker).toHaveAttribute('aria-pressed', 'true')
  await expect(page.locator('.vpa-relation-status')).toHaveText('ready to abstract one nullary occurrence')
})

test('mounted strip gestures reorder ports and consume Delete without touching canvas selection', async ({ page }) => {
  await openFixture(page)
  await page.evaluate(() => window.relationWorkspaceFixture.mount('substitute'))
  await spawnWorkspaceTerm(page, '\\v. v', 0.72)

  const initial = (await state(page)).debug!
  await expect(page.locator('.vpa-relation-port.is-optional')).toHaveCount(1)
  const loose = initial.draftWires.filter((wire) =>
    !wire.wire.startsWith('arg') && !initial.materializedBoundary.includes(wire.wire) && wire.point !== null)
  expect(loose).toHaveLength(1)
  await dropWireOnStrip(page, loose[0]!.wire)
  await expect(page.locator('.vpa-relation-port.is-optional')).toHaveCount(2)

  const beforeOrder = await page.locator('.vpa-relation-port.is-optional').evaluateAll((ports) =>
    ports.map((port) => (port as HTMLElement).dataset.wire!),
  )
  await page.locator('.vpa-relation-port.is-optional').first().focus()
  await page.keyboard.press('ArrowRight')
  const afterOrder = await page.locator('.vpa-relation-port.is-optional').evaluateAll((ports) =>
    ports.map((port) => (port as HTMLElement).dataset.wire!),
  )
  expect(afterOrder).toEqual([...beforeOrder].reverse())

  const forcedWire = (await state(page)).debug!.draftWires.find((wire) => wire.wire === 'arg1')!
  const historyBeforeInvalidCanvasEdit = (await state(page)).debug!.historyLength
  await page.mouse.click(forcedWire.point!.x, forcedWire.point!.y)
  await page.keyboard.press('Delete')
  expect((await state(page)).debug!.historyLength).toBe(historyBeforeInvalidCanvasEdit)
  expect((await state(page)).debug!.draftWires.some((wire) => wire.wire === 'arg1')).toBe(true)
  expect((await state(page)).refusals.at(-1)).toMatch(/boundary wire 'arg1' does not exist/i)

  const body = (await state(page)).debug!.draftBodies.find((candidate) => candidate.kind === 'term')!
  await page.mouse.click(body.point.x, body.point.y)
  const historyBeforeDelete = (await state(page)).debug!.historyLength
  await page.locator('.vpa-relation-port.is-optional').first().focus()
  await page.keyboard.press('Delete')
  await expect(page.locator('.vpa-relation-port.is-optional')).toHaveCount(1)
  expect((await state(page)).debug!.draftBodies.filter((candidate) => candidate.kind === 'term')).toHaveLength(2)
  expect((await state(page)).debug!.historyLength).toBe(historyBeforeDelete + 1)

  const historyBeforeForcedRefusal = (await state(page)).debug!.historyLength
  await page.locator('.vpa-relation-port.is-forced').focus()
  await page.keyboard.press('Backspace')
  await expect(page.locator('.vpa-relation-port.is-forced')).toHaveCount(1)
  expect((await state(page)).debug!.historyLength).toBe(historyBeforeForcedRefusal)
  expect((await state(page)).refusals.at(-1)).toMatch(/forced port.*cannot be deleted/i)

  const activeWire = (await state(page)).debug!.draftWires.find((wire) => wire.point !== null)!
  await page.mouse.move(activeWire.point!.x, activeWire.point!.y)
  await page.mouse.down()
  await page.mouse.move(activeWire.point!.x + 20, activeWire.point!.y + 20)
  await page.keyboard.press('Escape')
  await page.mouse.up()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('.vpa-relation-gesture')).toHaveCount(0)
  expect(await state(page)).toMatchObject({ cancelCount: 1, debug: null })
})

test('production abstraction statuses distinguish exhaustive, exhausted, invalid, stale, and kernel outcomes', async ({ page }) => {
  await openFixture(page)

  for (const configured of [
    { scenario: 'zero-match' as const, code: 'zero-match' },
    { scenario: 'matcher-exhausted' as const, code: 'matcher-exhausted' },
    { scenario: 'solver-exhausted' as const, code: 'solver-exhausted' },
    { scenario: 'invalid-ports' as const, code: 'invalid-ports' },
  ]) {
    await page.evaluate((scenario) => window.relationWorkspaceFixture.mountAbstractionScenario(scenario), configured.scenario)
    await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', configured.code)
    await expect(page.getByRole('button', { name: /Abstract|Instantiate/, exact: false })).toBeDisabled()
  }

  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('stale-source'))
  const staleBefore = (await state(page)).debug!
  await page.evaluate(() => window.relationWorkspaceFixture.staleSource())
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'stale-source')
  expect((await state(page)).debug).toMatchObject({
    cursor: staleBefore.cursor,
    historyLength: staleBefore.historyLength,
    draftBodies: staleBefore.draftBodies,
  })

  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('kernel-refusal'))
  const refusalBefore = (await state(page)).debug!
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'kernel-refusal')
  expect((await state(page)).debug).toMatchObject({
    cursor: refusalBefore.cursor,
    historyLength: refusalBefore.historyLength,
    draftBodies: refusalBefore.draftBodies,
  })
})

test('mounted abstraction captures marker geometry from the current scenario engine', async ({ page }) => {
  await openFixture(page)
  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('multi-set'))
  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('stale-source'))

  const point = (await state(page)).debug?.transaction?.markerPoint
  expect(point).not.toEqual({ x: 177, y: 93 })
  expect(Number.isFinite(point?.x)).toBe(true)
  expect(Number.isFinite(point?.y)).toBe(true)
})

test('mounted production multi-set transaction cycles exactly in both Tab directions', async ({ page }) => {
  await openFixture(page)
  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('multi-set'))
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'ready')
  expect((await state(page)).debug?.transaction).toMatchObject({ candidateCount: 6, activeIndex: 0 })

  await page.keyboard.press('Tab')
  expect((await state(page)).debug?.transaction?.activeIndex).toBe(1)
  await page.keyboard.press('Shift+Tab')
  expect((await state(page)).debug?.transaction?.activeIndex).toBe(0)
  await page.keyboard.press('Shift+Tab')
  expect((await state(page)).debug?.transaction?.activeIndex).toBe(2)
})
