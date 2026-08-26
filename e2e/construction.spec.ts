import { expect, loadTinyTheory, test, type TheoryFiles } from './zero-signature-fixture'
import type { Page } from '@playwright/test'

type Hit = { readonly kind: 'node' | 'region' | 'wire'; readonly id: string }
type Debug = {
  nodeCount(): number
  view(): { scale: number; offsetX: number; offsetY: number }
  bodies(): { id: string; kind: string; x: number; y: number; r: number; region: string }[]
  regions(): { id: string; kind: string; parent: string | null; x: number; y: number; r: number }[]
  wires(): { id: string; x: number; y: number; dx: number; dy: number }[]
  wireBinds(): { id: string; node: string; x: number; y: number }[]
  interactionOverlays(): string[]
  interaction(): { selected: readonly Hit[] }
  editJson(): string
  diagram(): {
    nodes: { id: string; kind: string; region: string }[]
    wires: { id: string; scope: string; endpoints: number }[]
    regions: { id: string; kind: string; parent: string | null }[]
  }
  dispose(): void
}

declare global {
  interface Window { __vpaDebug?: Debug }
}

async function openApp(page: Page, files: TheoryFiles): Promise<void> {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await loadTinyTheory(page, files)
}

async function canvasBox(page: Page) {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  return box
}

async function pagePoint(page: Page, world: { x: number; y: number }) {
  const box = await canvasBox(page)
  const view = await page.evaluate(() => window.__vpaDebug!.view())
  return {
    x: box.x + world.x * view.scale + view.offsetX,
    y: box.y + world.y * view.scale + view.offsetY,
  }
}

async function bodyPoint(page: Page, id: string) {
  const body = await page.evaluate((node) =>
    window.__vpaDebug!.bodies().find((candidate) => candidate.id === node)!, id)
  return pagePoint(page, body)
}

async function spawnRef(
  page: Page,
  at?: { readonly x: number; readonly y: number },
): Promise<void> {
  const box = await canvasBox(page)
  const count = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  const invocation = at ?? {
    x: box.x + box.width * (0.35 + (count % 3) * 0.15),
    y: box.y + box.height * (0.40 + (Math.floor(count / 3) % 2) * 0.16),
  }
  await page.mouse.click(invocation.x, invocation.y, { button: 'right' })
  const search = page.getByLabel('Search relation references to spawn')
  await search.fill('UnaryWitness')
  await search.press('Enter')
}

async function waitForNodes(page: Page, count: number): Promise<void> {
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(count)
}

test('the empty-region cascade spawns a Lambda term with one unary cap per incidence', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  const box = await canvasBox(page)
  await page.mouse.click(box.x + box.width * 0.55, box.y + box.height * 0.52, {
    button: 'right',
  })
  const cascade = page.locator('.vpa-spawn-cascade')
  const lambdaRow = cascade.getByRole('button', { name: 'Lambda expression', exact: true })
  await expect(lambdaRow).toBeVisible()
  await lambdaRow.click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill('(\\x. x) a')
  await input.press('Enter')

  await waitForNodes(page, 3)
  const stored = await page.evaluate(() => JSON.parse(window.__vpaDebug!.editJson()) as {
    nodes: Record<string, { kind: string; arity?: number; freeArity?: number; term?: string }>
    wires: Record<string, {
      sig: { kind: string }
      endpoints: { node: string; port: string }[]
    }>
  })
  const termEntry = Object.entries(stored.nodes).find(([, node]) => node.kind === 'term')
  expect(termEntry).toBeDefined()
  const [termId, term] = termEntry!
  const caps = Object.entries(stored.nodes)
    .filter(([, node]) => node.kind === 'identity' && node.arity === 1)
  expect(term.term).toBe('A(L(B(0)),F(0))')
  expect(term.freeArity).toBe(1)
  expect(caps).toHaveLength(2)
  expect(Object.keys(stored.nodes)).toHaveLength(3)
  expect(Object.values(stored.wires)).toHaveLength(2)
  for (const wire of Object.values(stored.wires)) {
    expect(wire.sig).toEqual({ kind: 'iota' })
    expect(wire.endpoints).toHaveLength(2)
    expect(wire.endpoints.some((endpoint) => endpoint.node === termId)).toBe(true)
    expect(wire.endpoints.some((endpoint) => (
      caps.some(([capId]) => endpoint.node === capId)
      && endpoint.port === 'i:0'
    ))).toBe(true)
  }
  expect(Object.values(stored.wires)
    .flatMap((wire) => wire.endpoints)
    .filter((endpoint) => endpoint.node === termId)
    .map((endpoint) => endpoint.port)
    .sort()).toEqual(['f:0', 'out'])
})

test('the structural spawn cascade is disposable and preserves selection', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await spawnRef(page)
  // UnaryWitness is arity 1: spawning a ref mints its own node plus a pin
  // holding the wire's other (open) end (spawn.ts's mintPin) — 2 nodes.
  await waitForNodes(page, 2)
  const node = await page.evaluate(() =>
    window.__vpaDebug!.bodies().find((body) => body.kind === 'ref')!.id)
  const nodeAt = await bodyPoint(page, node)
  await page.mouse.click(nodeAt.x, nodeAt.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected))
    .toEqual([{ kind: 'node', id: node }])

  const box = await canvasBox(page)
  const invocation = {
    x: box.x + box.width * 0.72,
    y: box.y + box.height * 0.68,
  }
  await page.mouse.click(invocation.x, invocation.y, { button: 'right' })
  await expect(page.locator('.vpa-spawn-cascade')).toBeVisible()
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected))
    .toEqual([{ kind: 'node', id: node }])
  await page.keyboard.press('Escape')
  await expect(page.locator('.vpa-spawn-cascade')).toHaveCount(0)

  await page.mouse.click(invocation.x, invocation.y, { button: 'right' })
  await page.locator('.vpa-spawn-backdrop').click({ position: { x: 4, y: 4 } })
  await expect(page.locator('.vpa-spawn-cascade')).toHaveCount(0)

  await spawnRef(page, invocation)
  // Two spawns of an arity-1 relation: 2 refs + 2 pins.
  await waitForNodes(page, 4)
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected))
    .toEqual([{ kind: 'node', id: node }])

  await page.evaluate(() => window.__vpaDebug!.dispose())
  await expect.poll(() => page.evaluate(() => window.__vpaDebug === undefined)).toBe(true)
  await expect(page.locator('#chrome')).toBeEmpty()
  await page.mouse.click(invocation.x, invocation.y, { button: 'right' })
  await expect(page.locator('.vpa-spawn-cascade')).toHaveCount(0)
})

test('one selected structural ref uses the shared contextual copy gesture', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await spawnRef(page)
  await spawnRef(page)
  // Two spawns of an arity-1 relation: 2 refs + 2 pins.
  await waitForNodes(page, 4)

  const loose = await page.evaluate(() => window.__vpaDebug!.wires())
  const sourceBind = await page.evaluate(() => window.__vpaDebug!.wireBinds()[0]!)
  expect(sourceBind).toBeDefined()
  const firstWire = await pagePoint(page, sourceBind)
  const secondWire = await pagePoint(page, loose.find((wire) => wire.id !== sourceBind.id)!)
  await page.mouse.move(firstWire.x, firstWire.y)
  await page.mouse.down()
  await page.mouse.move(secondWire.x, secondWire.y, { steps: 10 })
  await page.mouse.up()
  // wireJoin concatenates both wires' endpoint lists: 4 endpoints (ref, pin,
  // ref, pin) on the one surviving wire.
  await expect.poll(() =>
    page.evaluate(() => window.__vpaDebug!.diagram().wires.map((wire) => wire.endpoints)))
    .toEqual([4])

  const bodies = await page.evaluate(() =>
    window.__vpaDebug!.bodies().filter((body) => body.kind === 'ref'))
  const held = bodies[0]!
  const neighbour = bodies[1]!
  const heldPoint = await bodyPoint(page, held.id)
  const target = await pagePoint(page, neighbour)
  await page.mouse.click(heldPoint.x, heldPoint.y)
  await page.mouse.move(heldPoint.x, heldPoint.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interactionOverlays()))
    .toContain('circle')
  await page.mouse.up()
  // The shared contextual copy attaches the copied ref's port directly onto
  // the existing joined wire (now 5 endpoints) rather than minting a fresh
  // pin — one new node (the copy) on top of the 4 already present.
  await waitForNodes(page, 5)
  expect(await page.evaluate(({ held, neighbour }) => {
    const ids = window.__vpaDebug!.diagram().nodes.map((node) => node.id)
    return ids.includes(held) && ids.includes(neighbour)
  }, { held: held.id, neighbour: neighbour.id })).toBe(true)
})

test('a contextual structural spawn inside a cut belongs to that cut', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await spawnRef(page)
  // UnaryWitness is arity 1: spawning a ref mints its own node plus a pin
  // holding the wire's other (open) end — 2 nodes.
  await waitForNodes(page, 2)
  const original = await page.evaluate(() =>
    window.__vpaDebug!.bodies().find((body) => body.kind === 'ref')!.id)
  const originalAt = await bodyPoint(page, original)
  await page.mouse.click(originalAt.x, originalAt.y)
  await page.keyboard.press('w')
  await expect.poll(() =>
    page.evaluate(() => window.__vpaDebug!.diagram().regions
      .filter((region) => region.kind === 'cut').length)).toBe(1)

  const cut = await page.evaluate(() =>
    window.__vpaDebug!.regions().find((region) => region.kind === 'cut')!)
  // cutWrap reparents only the touched ref into the cut; the ref's pin holds
  // the wire's still-outer derived scope and is left at the root region, so
  // it is one of the "not original" nodes but does NOT belong to the cut.
  // Record every node id present before the contextual spawn so the newly
  // introduced ones (the second ref plus its own pin, both minted at the
  // spawn region per spawn.ts's mintPin) can be told apart from it.
  const before = await page.evaluate(() => window.__vpaDebug!.diagram().nodes.map((node) => node.id))
  const center = await pagePoint(page, cut)
  await spawnRef(page, center)
  await waitForNodes(page, 4)
  const structure = await page.evaluate(() => window.__vpaDebug!.diagram())
  const added = structure.nodes.filter((node) => !before.includes(node.id))
  expect(added).toHaveLength(2)
  for (const node of added) expect(node.region).toBe(cut.id)
})
