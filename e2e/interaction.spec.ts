import { expect, test, type Page } from '@playwright/test'

type Point = { readonly x: number; readonly y: number }
type Hit = { readonly kind: 'node' | 'region' | 'wire'; readonly id: string }
type Body = {
  readonly id: string
  readonly kind: string
  readonly x: number
  readonly y: number
  readonly r: number
  readonly region: string
}

type InteractionDebug = {
  readonly selected: readonly Hit[]
  readonly pins: readonly string[]
  readonly userZoom: number
}

type DebugHook = {
  view(): { readonly scale: number; readonly offsetX: number; readonly offsetY: number }
  bodies(): readonly Body[]
  regions(): readonly { id: string; kind: string; x: number; y: number; r: number }[]
  editForm(): string
  interaction(): InteractionDebug
}

type DebugWindow = Window & { __vpaDebug?: DebugHook }

async function openApp(page: Page): Promise<void> {
  await page.goto('/?debug')
  await page.waitForFunction(() => {
    const debug = (window as DebugWindow).__vpaDebug
    return debug !== undefined && typeof debug.interaction === 'function'
  })
}

async function addTerm(page: Page, source: string): Promise<void> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const count = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.bodies().filter((body) => body.kind === 'term').length)
  await page.mouse.click(
    box.x + box.width * (0.38 + (count % 3) * 0.12),
    box.y + box.height * (0.42 + (Math.floor(count / 3) % 2) * 0.14),
    { button: 'right' },
  )
  await page.getByRole('menu').getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill(source)
  await input.press('Enter')
}

async function addTwoTerms(page: Page): Promise<readonly [string, string]> {
  await addTerm(page, '\\x. x')
  await addTerm(page, '\\y. y')
  await expect.poll(async () => page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.bodies().filter((body) => body.kind === 'term').length,
  )).toBe(2)
  await waitForRest(page)
  const ids = await page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.bodies()
      .filter((body) => body.kind === 'term')
      .sort((a, b) => a.x - b.x)
      .map((body) => body.id),
  )
  return [ids[0]!, ids[1]!]
}

async function waitForRest(page: Page): Promise<void> {
  let previous = ''
  let stableSamples = 0
  await expect.poll(async () => {
    const signature = await page.evaluate(() => JSON.stringify(
      (window as DebugWindow).__vpaDebug!.bodies()
        .map((body) => [body.id, Math.round(body.x * 2), Math.round(body.y * 2)])
        .sort(([a], [b]) => String(a).localeCompare(String(b))),
    ))
    stableSamples = signature === previous ? stableSamples + 1 : 0
    previous = signature
    return stableSamples
  }, { timeout: 30_000, intervals: [200, 250, 300] }).toBeGreaterThanOrEqual(3)
}

async function canvasPointForBody(page: Page, id: string): Promise<Point> {
  return page.evaluate((bodyId) => {
    const debug = (window as DebugWindow).__vpaDebug!
    const body = debug.bodies().find((candidate) => candidate.id === bodyId)
    if (body === undefined) throw new Error(`body '${bodyId}' is not rendered`)
    const view = debug.view()
    return {
      x: body.x * view.scale + view.offsetX,
      y: body.y * view.scale + view.offsetY,
    }
  }, id)
}

async function pagePointForBody(page: Page, id: string): Promise<Point> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const local = await canvasPointForBody(page, id)
  return { x: box.x + local.x, y: box.y + local.y }
}

async function voidPoint(page: Page): Promise<Point> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  return { x: box.x + 24, y: box.y + box.height - 24 }
}

async function selected(page: Page): Promise<readonly Hit[]> {
  return page.evaluate(() => (window as DebugWindow).__vpaDebug!.interaction().selected)
}

async function pins(page: Page): Promise<readonly string[]> {
  return page.evaluate(() => (window as DebugWindow).__vpaDebug!.interaction().pins)
}

async function stroke(
  page: Page,
  from: Point,
  to: Point,
  modifiers: readonly ('Control' | 'Shift')[] = [],
): Promise<void> {
  await page.mouse.move(from.x, from.y)
  for (const modifier of modifiers) await page.keyboard.down(modifier)
  await page.mouse.down()
  await page.mouse.move(to.x, to.y, { steps: 16 })
  await page.mouse.up()
  for (const modifier of [...modifiers].reverse()) await page.keyboard.up(modifier)
}

async function physicsDrag(
  page: Page,
  from: Point,
  to: Point,
  pinOnRelease: boolean,
): Promise<void> {
  await page.mouse.move(from.x, from.y)
  await page.keyboard.down('Control')
  await page.mouse.down()
  await page.mouse.move(to.x, to.y, { steps: 16 })
  if (pinOnRelease) await page.keyboard.up('Control')
  await page.mouse.up()
  if (!pinOnRelease) await page.keyboard.up('Control')
}

test('brush adds and removes nodes, may start in the void, and a void click clears', async ({ page }) => {
  await openApp(page)
  const [leftId, rightId] = await addTwoTerms(page)
  const left = await pagePointForBody(page, leftId)
  const right = await pagePointForBody(page, rightId)

  // An add stroke paints every hit it crosses.
  await stroke(page, left, right)
  await expect.poll(async () => (await selected(page))
    .filter((hit) => hit.kind === 'node')
    .map((hit) => hit.id)
    .sort()).toEqual([leftId, rightId].sort())

  // Shift explicitly reserves the gesture for selection, even though an
  // unmodified drag on an already-selected node is direct placement in EDIT.
  await stroke(page, left, right, ['Shift'])
  await expect.poll(async () => (await selected(page))
    .filter((hit) => hit.kind === 'node')
    .map((hit) => hit.id)).toEqual([])

  // Empty space is a valid brush origin; touching an item makes this an add
  // stroke rather than the empty-click clear gesture.
  await stroke(page, await voidPoint(page), left)
  await expect.poll(async () => (await selected(page)).some((hit) => hit.kind === 'node' && hit.id === leftId)).toBe(true)

  const empty = await voidPoint(page)
  await page.mouse.click(empty.x, empty.y)
  await expect.poll(async () => selected(page)).toEqual([])
})

test('plain and Shift drags are selection-only while Ctrl-drag is physics-only', async ({ page }) => {
  await openApp(page)
  const [leftId, rightId] = await addTwoTerms(page)
  const semanticBefore = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.editForm())

  const left = await pagePointForBody(page, leftId)
  const plainTarget = { x: left.x + 110, y: left.y + 30 }
  await page.mouse.move(left.x, left.y)
  await page.mouse.down()
  await page.mouse.move(plainTarget.x, plainTarget.y, { steps: 16 })
  const heldAfterPlainDrag = await pagePointForBody(page, leftId)
  expect(Math.hypot(heldAfterPlainDrag.x - plainTarget.x, heldAfterPlainDrag.y - plainTarget.y)).toBeGreaterThan(45)
  await page.mouse.up()
  expect(await page.evaluate(() => (window as DebugWindow).__vpaDebug!.editForm())).toBe(semanticBefore)

  // Shift has precedence over every manipulation claim. Even Ctrl+Shift is a
  // brush stroke: it changes selection, never body geometry or semantics.
  await page.mouse.click((await voidPoint(page)).x, (await voidPoint(page)).y)
  const shiftStart = await pagePointForBody(page, leftId)
  const shiftEnd = await pagePointForBody(page, rightId)
  await stroke(page, shiftStart, shiftEnd, ['Control', 'Shift'])
  await expect.poll(async () => (await selected(page))
    .filter((hit) => hit.kind === 'node')
    .map((hit) => hit.id)
    .sort()).toEqual([leftId, rightId].sort())
  const leftAfterShift = await pagePointForBody(page, leftId)
  expect(Math.hypot(leftAfterShift.x - shiftEnd.x, leftAfterShift.y - shiftEnd.y)).toBeGreaterThan(35)
  expect(await page.evaluate(() => (window as DebugWindow).__vpaDebug!.editForm())).toBe(semanticBefore)
  expect(await pins(page)).toEqual([])

  // Ctrl alone claims physics. Sample while the button is held so passive
  // settling after release cannot disguise whether the drag was accepted. Move
  // into free interior space: an outward target would correctly stop at the
  // semantic frontier and would not be a cursor-tracking probe.
  const ctrlStart = await pagePointForBody(page, leftId)
  const ctrlTarget = { x: ctrlStart.x + 10, y: ctrlStart.y + 45 }
  await page.mouse.move(ctrlStart.x, ctrlStart.y)
  await page.keyboard.down('Control')
  await page.mouse.down()
  await page.mouse.move(ctrlTarget.x, ctrlTarget.y, { steps: 16 })
  const heldAfterCtrlDrag = await pagePointForBody(page, leftId)
  expect(Math.hypot(heldAfterCtrlDrag.x - ctrlTarget.x, heldAfterCtrlDrag.y - ctrlTarget.y)).toBeLessThan(25)
  await page.mouse.up()
  await page.keyboard.up('Control')
  expect(await page.evaluate(() => (window as DebugWindow).__vpaDebug!.editForm())).toBe(semanticBefore)
  expect(await pins(page)).toEqual([])
})

test('changing visible selection cancels a pending operation with an older source', async ({ page }) => {
  await openApp(page)
  const [leftId, rightId] = await addTwoTerms(page)
  const left = await pagePointForBody(page, leftId)
  const right = await pagePointForBody(page, rightId)

  await page.mouse.click(left.x, left.y)
  await page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true }).click()
  await expect(page.locator('#relation-name')).toBeVisible()

  // Tentative brush changes do not destroy the pending transaction. A browser
  // cancellation restores the old visible selection and the old pending UI.
  await page.mouse.move(right.x, right.y)
  await page.keyboard.down('Shift')
  await page.mouse.down()
  await page.evaluate(() => {
    document.querySelector<HTMLCanvasElement>('#c')!.dispatchEvent(new PointerEvent('pointercancel', {
      pointerId: 1,
      bubbles: true,
    }))
  })
  await page.mouse.up()
  await page.keyboard.up('Shift')
  await expect(page.locator('#relation-name')).toBeVisible()
  await expect.poll(async () => selected(page)).toEqual([{ kind: 'node', id: leftId }])

  await page.keyboard.down('Shift')
  await page.mouse.click(right.x, right.y)
  await page.keyboard.up('Shift')

  await expect(page.locator('#relation-name')).toHaveCount(0)
  await expect(page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true })).toBeVisible()
  await expect.poll(async () => (await selected(page))
    .filter((hit) => hit.kind === 'node')
    .map((hit) => hit.id)
    .sort()).toEqual([leftId, rightId].sort())
})

test('release order controls a node pin and moving it preserves unrelated pins', async ({ page }) => {
  await openApp(page)
  const [leftId, rightId] = await addTwoTerms(page)

  let left = await pagePointForBody(page, leftId)
  await physicsDrag(page, left, { x: left.x - 45, y: left.y + 25 }, true)
  await expect.poll(async () => [...await pins(page)].sort()).toEqual([leftId])

  let right = await pagePointForBody(page, rightId)
  await physicsDrag(page, right, { x: right.x + 45, y: right.y - 25 }, true)
  await expect.poll(async () => [...await pins(page)].sort()).toEqual([leftId, rightId].sort())

  // Beginning a new move releases only the moved node's pin. Keeping Ctrl held
  // through pointer-up chooses "leave unpinned"; the other node stays pinned.
  left = await pagePointForBody(page, leftId)
  await physicsDrag(page, left, { x: left.x + 35, y: left.y - 20 }, false)
  await expect.poll(async () => pins(page)).toEqual([rightId])

  // The opposite release order can pin the moved node again without disturbing
  // the independent pin that was already active.
  left = await pagePointForBody(page, leftId)
  await physicsDrag(page, left, { x: left.x - 25, y: left.y + 15 }, true)
  await expect.poll(async () => [...await pins(page)].sort()).toEqual([leftId, rightId].sort())

  // Diagram continuity is not a new interaction surface. Surviving pins and
  // the cursor-focused camera remain authoritative when an edit adds content.
  await page.mouse.move(left.x, left.y)
  await page.mouse.wheel(0, -450)
  const focusedView = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())
  await addTerm(page, '\\z. z')
  await expect.poll(async () => [...await pins(page)].sort()).toEqual([leftId, rightId].sort())
  const reconciledView = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())
  expect(Math.abs(reconciledView.scale - focusedView.scale)).toBeLessThan(0.001)
  expect(Math.abs(reconciledView.offsetX - focusedView.offsetX)).toBeLessThan(0.1)
  expect(Math.abs(reconciledView.offsetY - focusedView.offsetY)).toBeLessThan(0.1)
})

test('moving brush uses the cut ring and a cut drag can never create a node pin', async ({ page }) => {
  await openApp(page)
  await addTerm(page, '\\x. x')
  await waitForRest(page)
  const nodeId = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const node = await pagePointForBody(page, nodeId)
  await page.mouse.click(node.x, node.y)
  await page.keyboard.press('w')
  await waitForRest(page)

  const geometry = await page.evaluate(() => {
    const debug = (window as DebugWindow).__vpaDebug!
    const cut = debug.regions().find((region) => region.kind === 'cut')!
    const body = debug.bodies().find((candidate) => candidate.kind === 'term')!
    const view = debug.view()
    const angle = Math.atan2(cut.y - body.y, cut.x - body.x)
    const point = (distance: number) => ({
      x: (cut.x + Math.cos(angle) * distance) * view.scale + view.offsetX,
      y: (cut.y + Math.sin(angle) * distance) * view.scale + view.offsetY,
    })
    return {
      interior: point(Math.max(0, cut.r - 2)),
      ring: point(Math.max(0, cut.r - 0.2)),
    }
  })
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const interior = { x: box.x + geometry.interior.x, y: box.y + geometry.interior.y }
  const ring = { x: box.x + geometry.ring.x, y: box.y + geometry.ring.y }

  // A stationary interior click targets the cut, but once the pointer becomes
  // a brush stroke its origin is reclassified with moving/ring semantics.
  const empty = await voidPoint(page)
  await page.mouse.click(empty.x, empty.y)
  await stroke(page, interior, { x: interior.x + 10, y: interior.y })
  expect((await selected(page)).some((hit) => hit.kind === 'region')).toBe(false)

  // The same one-node cut used to lose its target provenance and pin its child.
  // Releasing Ctrl before pointer-up now produces the explicit refusal instead.
  await physicsDrag(page, ring, { x: ring.x + 35, y: ring.y + 10 }, true)
  await expect.poll(async () => pins(page)).toEqual([])
  await expect(page.locator('#status')).toContainText('not pinned')
})

test('pointer-up is an authoritative physics sample without an intermediate move event', async ({ page }) => {
  await openApp(page)
  await addTerm(page, '\\x. x')
  await waitForRest(page)
  const id = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const start = await pagePointForBody(page, id)
  const target = { x: start.x + 10, y: start.y + 35 }
  const cdp = await page.context().newCDPSession(page)

  await cdp.send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: start.x, y: start.y })
  await cdp.send('Input.dispatchMouseEvent', {
    type: 'mousePressed', x: start.x, y: start.y, button: 'left', buttons: 1,
    clickCount: 1, modifiers: 2,
  })
  await cdp.send('Input.dispatchMouseEvent', {
    type: 'mouseReleased', x: target.x, y: target.y, button: 'left', buttons: 0,
    clickCount: 1, modifiers: 0,
  })

  await expect.poll(async () => pins(page)).toEqual([id])
  const dropped = await pagePointForBody(page, id)
  expect(Math.hypot(dropped.x - target.x, dropped.y - target.y)).toBeLessThan(25)
})

test('pointer cancellation rolls selection, body position, and released pins back', async ({ page }) => {
  await openApp(page)
  const [leftId, rightId] = await addTwoTerms(page)
  let left = await pagePointForBody(page, leftId)
  await physicsDrag(page, left, { x: left.x - 30, y: left.y + 15 }, true)
  await expect.poll(async () => pins(page)).toEqual([leftId])
  left = await pagePointForBody(page, leftId)

  await page.mouse.move(left.x, left.y)
  await page.keyboard.down('Control')
  await page.mouse.down()
  await page.mouse.move(left.x + 35, left.y + 25, { steps: 8 })
  await expect.poll(async () => pins(page)).toEqual([])
  await page.evaluate(() => {
    document.querySelector<HTMLCanvasElement>('#c')!.dispatchEvent(new PointerEvent('pointercancel', {
      pointerId: 1,
      bubbles: true,
    }))
  })
  await page.mouse.up()
  await page.keyboard.up('Control')
  await expect.poll(async () => pins(page)).toEqual([leftId])
  const restored = await pagePointForBody(page, leftId)
  expect(Math.hypot(restored.x - left.x, restored.y - left.y)).toBeLessThan(2)

  const right = await pagePointForBody(page, rightId)
  await page.mouse.move(right.x, right.y)
  await page.mouse.down()
  await page.mouse.move(left.x, left.y, { steps: 8 })
  expect((await selected(page)).length).toBeGreaterThan(0)
  await page.evaluate(() => {
    document.querySelector<HTMLCanvasElement>('#c')!.dispatchEvent(new PointerEvent('pointercancel', {
      pointerId: 1,
      bubbles: true,
    }))
  })
  await page.mouse.up()
  await expect.poll(async () => selected(page)).toEqual([])
})

test('a logical surface change resets interaction even when it reuses the same diagram object', async ({ page }) => {
  await openApp(page)
  await addTerm(page, '\\x. x')
  await waitForRest(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()

  const id = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  let node = await pagePointForBody(page, id)
  await physicsDrag(page, node, { x: node.x + 25, y: node.y + 20 }, true)
  await expect.poll(async () => pins(page)).toEqual([id])
  node = await pagePointForBody(page, id)
  await page.mouse.click(node.x, node.y)
  await page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true }).click()
  await expect(page.locator('#relation-name')).toBeVisible()

  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  await page.mouse.move(box.x + 80, box.y + 80)
  await page.mouse.wheel(0, -400)
  const focused = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())

  await page.getByRole('button', { name: 'Switch to PROVE', exact: true }).click()

  await expect(page.locator('#status')).toContainText('[PROVE')
  await expect.poll(async () => pins(page)).toEqual([])
  await expect.poll(async () => selected(page)).toEqual([])
  await expect(page.locator('#relation-name')).toHaveCount(0)
  const reset = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())
  expect(Math.hypot(reset.offsetX - focused.offsetX, reset.offsetY - focused.offsetY)).toBeGreaterThan(5)
})

test('wheel zoom stays under the cursor and cannot zoom out beyond full-boundary fit', async ({ page }) => {
  await openApp(page)
  const [leftId] = await addTwoTerms(page)
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')

  const anchor = await pagePointForBody(page, leftId)
  const localAnchor = { x: anchor.x - box.x, y: anchor.y - box.y }
  const before = await page.evaluate(({ x, y }) => {
    const view = (window as DebugWindow).__vpaDebug!.view()
    return {
      world: { x: (x - view.offsetX) / view.scale, y: (y - view.offsetY) / view.scale },
      zoom: (window as DebugWindow).__vpaDebug!.interaction().userZoom,
    }
  }, localAnchor)

  await page.mouse.move(anchor.x, anchor.y)
  await page.mouse.wheel(0, -650)
  await expect.poll(async () => page.evaluate(() => (window as DebugWindow).__vpaDebug!.interaction().userZoom)).toBeGreaterThan(before.zoom)
  const anchoredAfter = await page.evaluate(({ world, screen }) => {
    const view = (window as DebugWindow).__vpaDebug!.view()
    return {
      x: world.x * view.scale + view.offsetX - screen.x,
      y: world.y * view.scale + view.offsetY - screen.y,
    }
  }, { world: before.world, screen: localAnchor })
  expect(Math.hypot(anchoredAfter.x, anchoredAfter.y)).toBeLessThan(2)

  // A very large outward wheel delta reaches the canonical full fit. Further
  // outward deltas are inert: they cannot shrink or offset the boundary.
  await page.mouse.wheel(0, 100_000)
  await expect.poll(async () => page.evaluate(() => (window as DebugWindow).__vpaDebug!.interaction().userZoom)).toBe(1)
  const minimum = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())
  await page.mouse.move(box.x + box.width - 40, box.y + 40)
  await page.mouse.wheel(0, 100_000)
  const beyondMinimum = await page.evaluate(() => (window as DebugWindow).__vpaDebug!.view())
  expect(Math.abs(beyondMinimum.scale - minimum.scale)).toBeLessThan(0.001)
  expect(Math.abs(beyondMinimum.offsetX - minimum.offsetX)).toBeLessThan(0.1)
  expect(Math.abs(beyondMinimum.offsetY - minimum.offsetY)).toBeLessThan(0.1)
})
