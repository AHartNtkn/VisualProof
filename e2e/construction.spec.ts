import { expect, test, type Page } from '@playwright/test'

type Hit = { readonly kind: 'node' | 'region' | 'wire'; readonly id: string }
type Debug = {
  nodeCount(): number
  view(): { scale: number; offsetX: number; offsetY: number }
  bodies(): { id: string; kind: string; x: number; y: number; region: string }[]
  regions(): { id: string; kind: string; parent: string | null; x: number; y: number; r: number }[]
  wires(): { id: string; x: number; y: number; dx: number; dy: number }[]
  wireBinds(): { id: string; node: string; x: number; y: number }[]
  interaction(): { selected: readonly Hit[] }
  diagram(): {
    nodes: { id: string; kind: string; region: string; defId: string | null; binder: string | null }[]
    wires: { id: string; scope: string; endpoints: number }[]
    regions: { id: string; kind: string; parent: string | null }[]
  }
  spawnBinderHover(): string | null
  dispose(): void
}

declare global {
  interface Window { __vpaDebug?: Debug }
}

async function openApp(page: Page): Promise<void> {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
}

async function canvasBox(page: Page) {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  return box
}

async function spawnTerm(page: Page, source: string, at?: { x: number; y: number }): Promise<void> {
  const box = await canvasBox(page)
  const count = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  const invocation = at ?? {
    x: box.x + box.width * (0.35 + (count % 3) * 0.15),
    y: box.y + box.height * (0.40 + (Math.floor(count / 3) % 2) * 0.16),
  }
  await page.mouse.click(invocation.x, invocation.y, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill(source)
  await input.press('Enter')
}

async function pagePoint(page: Page, world: { x: number; y: number }) {
  const box = await canvasBox(page)
  const view = await page.evaluate(() => window.__vpaDebug!.view())
  return { x: box.x + world.x * view.scale + view.offsetX, y: box.y + world.y * view.scale + view.offsetY }
}

async function bodyPoint(page: Page, id: string) {
  const body = await page.evaluate((node) => window.__vpaDebug!.bodies().find((candidate) => candidate.id === node)!, id)
  return pagePoint(page, body)
}

async function waitForNodes(page: Page, count: number): Promise<void> {
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(count)
  await waitForRest(page)
}

async function waitForRest(page: Page): Promise<void> {
  let previous = ''
  let stable = 0
  await expect.poll(async () => {
    const signature = await page.evaluate(() => JSON.stringify({
      bodies: window.__vpaDebug!.bodies().map((body) => [body.id, Math.round(body.x * 2), Math.round(body.y * 2)]),
      regions: window.__vpaDebug!.regions().map((region) => [region.id, Math.round(region.x * 2), Math.round(region.y * 2), Math.round(region.r * 2)]),
      wires: window.__vpaDebug!.wires().map((wire) => [wire.id, Math.round(wire.x * 2), Math.round(wire.y * 2)]),
    }))
    stable = signature === previous ? stable + 1 : 0
    previous = signature
    return stable
  }, { timeout: 30_000, intervals: [150, 200, 250] }).toBeGreaterThanOrEqual(3)
}

test('the contextual spawn cascade is disposable and preserves the construction selection', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const node = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const nodeAt = await bodyPoint(page, node)
  await page.mouse.click(nodeAt.x, nodeAt.y)
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([{ kind: 'node', id: node }])

  const box = await canvasBox(page)
  const invoke = { x: box.x + box.width * 0.72, y: box.y + box.height * 0.68 }
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await expect(page.locator('.vpa-spawn-column')).toBeVisible()
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([{ kind: 'node', id: node }])
  await page.keyboard.press('Escape')
  await expect(page.locator('.vpa-spawn-column')).toHaveCount(0)

  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.locator('.vpa-spawn-backdrop').click({ position: { x: 4, y: 4 } })
  await expect(page.locator('.vpa-spawn-column')).toHaveCount(0)

  await spawnTerm(page, '\\y. y', invoke)
  await waitForNodes(page, 2)
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([{ kind: 'node', id: node }])

  await page.evaluate(() => window.__vpaDebug!.dispose())
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug === undefined)).toBe(true)
  await expect(page.locator('#chrome')).toBeEmpty()
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await expect(page.locator('.vpa-spawn-column')).toHaveCount(0)
})

test('spawns, identifies, highlights, and undoes a predicate bound to the enclosing bubble', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const term = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const termAt = await bodyPoint(page, term)
  await page.mouse.click(termAt.x, termAt.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('2')
  await page.getByLabel('Bubble arity').press('Enter')
  await waitForRest(page)
  const bubble = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!)
  const openAt = await pagePoint(page, { x: bubble.x + bubble.r * 0.55, y: bubble.y })
  await page.mouse.click(openAt.x, openAt.y, { button: 'right' })

  const option = page.locator('.vpa-spawn-bound-predicate')
  await expect(option).toHaveCount(1)
  await expect(option).toContainText('Bound predicate')
  await expect(option).toContainText('/2')
  await expect(page.locator('.vpa-spawn-binder-swatch')).toHaveCSS('background-color', /rgb/)
  await option.hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(bubble.id)
  await option.click()

  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.diagram().nodes.filter((node) => node.kind === 'atom'))).toEqual([
    expect.objectContaining({ kind: 'atom', region: bubble.id, binder: bubble.id }),
  ])
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  expect((await page.evaluate(() => window.__vpaDebug!.diagram())).wires.filter((wire) =>
    wire.scope === bubble.id && wire.endpoints === 1,
  )).toHaveLength(3)

  await page.getByRole('button', { name: 'Undo', exact: true }).click()
  await expect.poll(() => page.evaluate(() =>
    window.__vpaDebug!.diagram().nodes.some((node) => node.kind === 'atom'),
  )).toBe(false)
})

test('nested bound-predicate choices identify their bubbles by order, color, and hover', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const term = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const termAt = await bodyPoint(page, term)
  await page.mouse.click(termAt.x, termAt.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('1')
  await page.getByLabel('Bubble arity').press('Enter')
  await waitForRest(page)

  const innerBefore = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!)
  const innerInterior = await pagePoint(page, { x: innerBefore.x + innerBefore.r * 0.8, y: innerBefore.y })
  await page.mouse.click(innerInterior.x, innerInterior.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([
    { kind: 'region', id: innerBefore.id },
  ])
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('2')
  await page.getByLabel('Bubble arity').press('Enter')
  await waitForRest(page)

  const bubbles = await page.evaluate(() => window.__vpaDebug!.regions().filter((region) => region.kind === 'bubble'))
  const inner = bubbles.find((bubble) => bubble.parent !== 'r0')!
  const outer = bubbles.find((bubble) => bubble.parent === 'r0')!
  const invoke = await pagePoint(page, { x: inner.x + inner.r * 0.55, y: inner.y })
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })

  const rows = page.locator('.vpa-spawn-bound-predicate')
  await expect(rows).toHaveCount(2)
  await expect(rows.nth(0)).toContainText('Binder 1 (innermost)')
  await expect(rows.nth(0)).toContainText('/1')
  await expect(rows.nth(1)).toContainText('Binder 2 (outermost)')
  await expect(rows.nth(1)).toContainText('/2')
  const swatches = page.locator('.vpa-spawn-binder-swatch')
  expect(await swatches.nth(0).evaluate((element) => getComputedStyle(element).backgroundColor))
    .not.toBe(await swatches.nth(1).evaluate((element) => getComputedStyle(element).backgroundColor))

  await rows.nth(0).hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(inner.id)
  await rows.nth(1).hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBe(outer.id)
  await page.getByLabel('Search relations to spawn').hover()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  await rows.nth(0).hover()
  await page.keyboard.press('Escape')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.spawnBinderHover())).toBeNull()
  await expect(rows).toHaveCount(0)
})

test('selected-node placement holds the pointer while connected physics remains live', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await spawnTerm(page, '\\y. y')
  await waitForNodes(page, 2)

  const loose = await page.evaluate(() => window.__vpaDebug!.wires())
  const sourceBind = await page.evaluate(() => window.__vpaDebug!.wireBinds()[0]!)
  expect(sourceBind).toBeDefined()
  const firstWire = await pagePoint(page, sourceBind)
  const secondWire = await pagePoint(page, loose.find((wire) => wire.id !== sourceBind.id)!)
  await page.mouse.move(firstWire.x, firstWire.y)
  await page.mouse.down()
  await page.mouse.move(secondWire.x, secondWire.y, { steps: 10 })
  await page.mouse.up()
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().wires.map((wire) => wire.endpoints))).toEqual([2])
  await waitForRest(page)

  const bodies = await page.evaluate(() => window.__vpaDebug!.bodies().filter((body) => body.kind === 'term'))
  const held = bodies[0]!
  const neighbour = bodies[1]!
  const heldPoint = await bodyPoint(page, held.id)
  const target = await pagePoint(page, neighbour)
  await page.mouse.click(heldPoint.x, heldPoint.y)
  const neighbourBeforeDrag = await page.evaluate((id) => window.__vpaDebug!.bodies().find((body) => body.id === id)!, neighbour.id)
  await page.mouse.move(heldPoint.x, heldPoint.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y)
  const before = await page.evaluate(({ held, neighbour }) => {
    const bodies = window.__vpaDebug!.bodies()
    return {
      held: bodies.find((body) => body.id === held)!,
      neighbour: bodies.find((body) => body.id === neighbour)!,
    }
  }, { held: held.id, neighbour: neighbour.id })
  await page.waitForTimeout(450)
  const after = await page.evaluate(({ held, neighbour }) => {
    const bodies = window.__vpaDebug!.bodies()
    return {
      held: bodies.find((body) => body.id === held)!,
      neighbour: bodies.find((body) => body.id === neighbour)!,
    }
  }, { held: held.id, neighbour: neighbour.id })
  expect(Math.hypot(after.held.x - before.held.x, after.held.y - before.held.y)).toBeLessThan(0.01)
  expect(Math.hypot(after.neighbour.x - neighbourBeforeDrag.x, after.neighbour.y - neighbourBeforeDrag.y)).toBeGreaterThan(0.01)
  await page.mouse.up()
})

test('direct EDIT gestures wrap, reparent, join, sever, and dissolve semantic objects', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await spawnTerm(page, '\\y. y')
  await spawnTerm(page, '\\z. z')
  await waitForNodes(page, 3)
  const ids = await page.evaluate(() => window.__vpaDebug!.bodies().filter((body) => body.kind === 'term').map((body) => body.id))

  // W draws one construction cut around the current selection.
  let at = await bodyPoint(page, ids[0]!)
  await page.mouse.click(at.x, at.y)
  await page.keyboard.press('w')
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().regions.filter((region) => region.kind === 'cut').length)).toBe(1)
  const cut = await page.evaluate(() => window.__vpaDebug!.diagram().regions.find((region) => region.kind === 'cut')!)
  expect((await page.evaluate(() => window.__vpaDebug!.diagram())).nodes.find((node) => node.id === ids[0])!.region).toBe(cut.id)

  // Select, then drag: direct placement reparents into the destination region.
  at = await bodyPoint(page, ids[1]!)
  await page.mouse.click(at.x, at.y)
  const cutGeometry = await page.evaluate((id) => window.__vpaDebug!.regions().find((region) => region.id === id)!, cut.id)
  const cutCenter = await pagePoint(page, cutGeometry)
  await page.mouse.move(at.x, at.y)
  await page.mouse.down()
  await page.mouse.move(cutCenter.x, cutCenter.y, { steps: 12 })
  await page.mouse.up()
  await expect.poll(async () => page.evaluate((id) => window.__vpaDebug!.diagram().nodes.find((node) => node.id === id)!.region, ids[1]!)).toBe(cut.id)

  // Shift-W requests the bubble's semantic arity at the point of use.
  at = await bodyPoint(page, ids[2]!)
  await page.mouse.click(at.x, at.y)
  await page.keyboard.press('Shift+w')
  const arity = page.getByLabel('Bubble arity')
  await arity.fill('1')
  await arity.press('Enter')
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().regions.filter((region) => region.kind === 'bubble').length)).toBe(1)

  // Dragging one line onto another joins the two ports into one individual.
  await waitForRest(page)
  const insideWireIds = await page.evaluate((region) => window.__vpaDebug!.diagram().wires.filter((wire) => wire.scope === region).map((wire) => wire.id), cut.id)
  expect(insideWireIds).toHaveLength(2)
  const rendered = await page.evaluate(() => window.__vpaDebug!.wires())
  const first = rendered.find((wire) => wire.id === insideWireIds[0])!
  const second = rendered.find((wire) => wire.id === insideWireIds[1])!
  const firstAt = await pagePoint(page, first)
  const secondAt = await pagePoint(page, second)
  await page.mouse.move(firstAt.x, firstAt.y)
  await page.mouse.down()
  await page.mouse.move(secondAt.x, secondAt.y, { steps: 12 })
  await page.mouse.up()
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().wires.some((wire) => wire.endpoints === 2))).toBe(true)

  // J joins every selected line, including the remaining bubble-port line.
  await waitForRest(page)
  const twoWires = await page.evaluate(() => {
    const semantic = window.__vpaDebug!.diagram().wires.map((wire) => wire.id)
    const rendered = window.__vpaDebug!.wires()
    return semantic.map((id) => rendered.find((wire) => wire.id === id)!)
  })
  for (const wire of twoWires) {
    const point = await pagePoint(page, wire)
    await page.mouse.click(point.x, point.y)
  }
  await page.keyboard.press('j')
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().wires.map((wire) => wire.endpoints))).toEqual([3])

  // A perpendicular right-drag across a real rendered leg severs one endpoint.
  await waitForRest(page)
  const joined = await page.evaluate(() => {
    const semantic = window.__vpaDebug!.diagram().wires.find((wire) => wire.endpoints === 3)!
    return window.__vpaDebug!.wires().find((wire) => wire.id === semantic.id)!
  })
  const joinedAt = await pagePoint(page, joined)
  const length = Math.hypot(joined.dx, joined.dy)
  const px = length === 0 ? 0 : -joined.dy / length * 24
  const py = length === 0 ? 24 : joined.dx / length * 24
  await page.mouse.move(joinedAt.x - px, joinedAt.y - py)
  await page.mouse.down({ button: 'right' })
  await page.mouse.move(joinedAt.x + px, joinedAt.y + py, { steps: 10 })
  await page.mouse.up({ button: 'right' })
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().wires.map((wire) => wire.endpoints).sort())).toEqual([1, 2])

  // The options toggle exposes the accepted double-click alternative without
  // changing the default slash gesture.
  await page.getByRole('button', { name: /⚙ sever: right-drag slash/ }).click()
  await waitForRest(page)
  const remainingJoined = await page.evaluate(() => {
    const semantic = window.__vpaDebug!.diagram().wires.find((wire) => wire.endpoints === 2)!
    return window.__vpaDebug!.wires().find((wire) => wire.id === semantic.id)!
  })
  const remainingAt = await pagePoint(page, remainingJoined)
  await page.mouse.dblclick(remainingAt.x, remainingAt.y)
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().wires.map((wire) => wire.endpoints).sort())).toEqual([1, 1, 1])

  // Delete on a boundary dissolves it and promotes all unselected contents.
  const liveCut = await page.evaluate((id) => window.__vpaDebug!.regions().find((region) => region.id === id)!, cut.id)
  let selectedCut = false
  const box = await canvasBox(page)
  for (let i = 0; i < 24 && !selectedCut; i++) {
    const angle = i * Math.PI * 2 / 24
    const ring = await pagePoint(page, {
      x: liveCut.x + Math.cos(angle) * liveCut.r,
      y: liveCut.y + Math.sin(angle) * liveCut.r,
    })
    await page.mouse.click(ring.x, ring.y)
    selectedCut = await page.evaluate((id) => window.__vpaDebug!.interaction().selected.some((hit) => hit.kind === 'region' && hit.id === id), cut.id)
    if (!selectedCut) await page.mouse.click(box.x + 20, box.y + box.height - 20)
  }
  expect(selectedCut).toBe(true)
  await page.keyboard.press('Delete')
  await expect.poll(async () => page.evaluate((id) => window.__vpaDebug!.diagram().regions.some((region) => region.id === id), cut.id)).toBe(false)
  const structure = await page.evaluate(() => window.__vpaDebug!.diagram())
  expect(structure.nodes.filter((node) => ids.slice(0, 2).includes(node.id)).every((node) => node.region === 'r0')).toBe(true)
})

test('a contextual spawn inside a cut belongs to that cut', async ({ page }) => {
  await openApp(page)
  await spawnTerm(page, '\\x. x')
  await waitForNodes(page, 1)
  const original = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term')!.id)
  const originalAt = await bodyPoint(page, original)
  await page.mouse.click(originalAt.x, originalAt.y)
  await page.keyboard.press('w')
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.diagram().regions.filter((region) => region.kind === 'cut').length)).toBe(1)
  await waitForRest(page)

  const cut = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'cut')!)
  const center = await pagePoint(page, cut)
  await page.mouse.click(center.x, center.y, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill('\\y. y')
  await input.press('Enter')
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(2)
  const structure = await page.evaluate(() => window.__vpaDebug!.diagram())
  const added = structure.nodes.find((node) => node.id !== original)!
  expect(added.region).toBe(cut.id)
})
