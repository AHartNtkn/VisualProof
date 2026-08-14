import type { Page } from '@playwright/test'
import {
  expect,
  loadTinyTheory,
  test,
  type TheoryFiles,
} from './zero-signature-fixture'

type Point = { readonly x: number; readonly y: number }
type Body = {
  readonly id: string
  readonly kind: string
  readonly x: number
  readonly y: number
  readonly r: number
  readonly region: string
}

type ProofFrontDebug = {
  readonly view: { readonly scale: number; readonly offsetX: number; readonly offsetY: number }
  readonly bodies: readonly Body[]
  readonly regionCount: number
  readonly nodeCount: number
  readonly wireCount: number
  readonly binds: readonly { id: string; node: string; x: number; y: number }[]
}

type DebugHook = {
  bodies(): readonly Body[]
  wires(): readonly { id: string; x: number; y: number }[]
  wireBinds(): readonly { id: string; node: string; x: number; y: number }[]
  view(): { readonly scale: number; readonly offsetX: number; readonly offsetY: number }
  proofFront(side: 'forward' | 'backward'): ProofFrontDebug
}

type DebugWindow = Window & { __vpaDebug?: DebugHook }

async function openApp(page: Page, files: TheoryFiles): Promise<void> {
  await page.goto('/?debug')
  await page.waitForFunction(() => {
    const debug = (window as DebugWindow).__vpaDebug
    return debug !== undefined && typeof debug.proofFront === 'function'
  })
  await loadTinyTheory(page, files)
}

async function addRef(page: Page): Promise<void> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const count = await page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.bodies().filter((body) => body.kind === 'ref').length)
  await page.mouse.click(
    box.x + box.width * (0.38 + (count % 3) * 0.12),
    box.y + box.height * (0.42 + (Math.floor(count / 3) % 2) * 0.14),
    { button: 'right' },
  )
  const search = page.getByLabel('Search relation references to spawn')
  await search.fill('UnaryWitness')
  await search.press('Enter')
}

async function waitForFrontRest(page: Page): Promise<void> {
  let previous = ''
  let stableSamples = 0
  await expect.poll(async () => {
    const signature = await page.evaluate(() => JSON.stringify(
      (window as DebugWindow).__vpaDebug!.proofFront('forward').bodies
        .map((body) => [body.id, Math.round(body.x * 2), Math.round(body.y * 2)])
        .sort(([a], [b]) => String(a).localeCompare(String(b))),
    ))
    stableSamples = signature === previous ? stableSamples + 1 : 0
    previous = signature
    return stableSamples
  }, { timeout: 30_000, intervals: [200, 250, 300] }).toBeGreaterThanOrEqual(3)
}

const FRONT = '[aria-label="forward proof front"]'

async function frontBox(page: Page): Promise<{ x: number; y: number; width: number; height: number }> {
  const box = await page.locator(FRONT).boundingBox()
  if (box === null) throw new Error('the forward proof front has no bounding box')
  return box
}

/** Screen point for a world point of the forward front. */
async function frontPoint(page: Page, world: Point): Promise<Point> {
  const box = await frontBox(page)
  const view = await page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.proofFront('forward').view)
  return {
    x: box.x + world.x * view.scale + view.offsetX,
    y: box.y + world.y * view.scale + view.offsetY,
  }
}

/** Enter prove mode over the current construction as both goal sides. */
async function proveCurrent(page: Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()
  await expect(page.locator('#status')).toContainText('[PROVE')
  await waitForFrontRest(page)
}

/** Construct an applied atom: select the ref, declare a unary relation
    wire (Shift+W arity prompt), then spawn an atom on it. */
async function addAtom(page: Page): Promise<void> {
  const ref = await page.evaluate(() => {
    const body = (window as DebugWindow).__vpaDebug!.bodies()
      .find((candidate) => candidate.kind === 'ref')
    if (body === undefined) throw new Error('no ref to anchor the relation wire')
    const view = (window as DebugWindow).__vpaDebug!.view()
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  await page.mouse.click(box.x + ref.x, box.y + ref.y)
  await page.keyboard.press('Shift+W')
  const arity = page.getByLabel('Relation arity')
  await arity.fill('1')
  await arity.press('Enter')
  await page.mouse.click(box.x + 60, box.y + 60, { button: 'right' })
  await page.getByRole('button', { name: /Atom on visible relation/ }).click()
  await expect.poll(() => page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.bodies()
      .filter((body) => body.kind === 'atom').length)).toBe(1)
}

async function counts(page: Page): Promise<{ regions: number; wires: number; nodes: number }> {
  return page.evaluate(() => {
    const front = (window as DebugWindow).__vpaDebug!.proofFront('forward')
    return { regions: front.regionCount, wires: front.wireCount, nodes: front.nodeCount }
  })
}

async function rightDrag(page: Page, from: Point, to: Point): Promise<void> {
  await page.mouse.move(from.x, from.y)
  await page.mouse.down({ button: 'right' })
  await page.mouse.move(to.x, to.y, { steps: 12 })
  await page.mouse.up({ button: 'right' })
}

/** A blank spot in the front pane, biased to a corner away from content. */
async function blankPoint(page: Page, dx = 26, dy = 26): Promise<Point> {
  const box = await frontBox(page)
  return { x: box.x + dx, y: box.y + box.height - dy }
}

test('W with an empty selection spawns a double cut at the hovered region', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await addRef(page)
  await proveCurrent(page)
  const before = await counts(page)

  const blank = await blankPoint(page)
  await page.mouse.click(blank.x, blank.y)
  await page.mouse.move(blank.x + 4, blank.y - 4)
  await page.keyboard.press('w')

  await expect.poll(async () => (await counts(page)).regions)
    .toBe(before.regions + 2)
})

test('a plain right-click opens the palette; a drawn right-drag suppresses it', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await addRef(page)
  await proveCurrent(page)

  // A founding right-drag draws and never opens the palette.
  const blank = await blankPoint(page)
  await rightDrag(page, blank, { x: blank.x + 70, y: blank.y - 50 })
  await expect(page.getByLabel('Search relation references to spawn')).toHaveCount(0)
  // Cancel the pending drawing; a still right-click then opens the palette.
  await page.keyboard.press('Escape')
  await page.mouse.click(blank.x, blank.y, { button: 'right' })
  await expect(page.getByLabel('Search relation references to spawn')).toBeVisible()
  await page.keyboard.press('Escape')
})

test('the drawing gesture severs a shared wire at a touched end', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await addRef(page)
  await addRef(page)
  await expect.poll(async () => page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.bodies().filter((body) => body.kind === 'ref').length,
  )).toBe(2)
  // Join the two argument wires into one shared wire (construction merge).
  const editBox = await page.locator('#c').boundingBox()
  if (editBox === null) throw new Error('the main canvas has no bounding box')
  const endpoints = await page.evaluate(() => {
    const debug = (window as DebugWindow).__vpaDebug!
    const source = debug.wireBinds()[0]
    if (source === undefined) throw new Error('the first ref has no rendered wire binding')
    const target = debug.wires().find((wire) => wire.id !== source.id)
    if (target === undefined) throw new Error('the second ref has no rendered loose wire')
    const view = debug.view()
    const screen = (point: { readonly x: number; readonly y: number }) => ({
      x: point.x * view.scale + view.offsetX,
      y: point.y * view.scale + view.offsetY,
    })
    return { source: screen(source), target: screen(target) }
  })
  await page.mouse.move(editBox.x + endpoints.source.x, editBox.y + endpoints.source.y)
  await page.mouse.down()
  await page.mouse.move(editBox.x + endpoints.target.x, editBox.y + endpoints.target.y, { steps: 10 })
  await page.mouse.up()
  // wireJoin merges the two 2-end wires (ref+pin each) into one wire whose
  // endpoint list is the concatenation of both: 4 endpoints (ref, pin, ref,
  // pin), all node-bound — every one of them is a rendered wireBind.
  await expect.poll(() => page.evaluate(() =>
    (window as DebugWindow).__vpaDebug!.wireBinds().length)).toBe(4)
  await proveCurrent(page)
  const before = await counts(page)

  // Found a drawing whose stroke releases on one bound endpoint of the
  // shared wire, then drop the loose end in open space: end-partition sever.
  // Every wire end is now a node (ref or pin), so the joined wire has four
  // binds (two refs, two pins), not two — a bind on a pin would dispatch to
  // identityAbstract (draw.ts's 'identity' contact kind), not wireSever, so
  // the touched end must specifically be one of the wire's two ref binds.
  const bind = await page.evaluate(() => {
    const front = (window as DebugWindow).__vpaDebug!.proofFront('forward')
    const kindOf = new Map(front.bodies.map((body) => [body.id, body.kind]))
    const byWire = new Map<string, { refs: { x: number; y: number }[] }>()
    for (const candidate of front.binds) {
      if (kindOf.get(candidate.node) !== 'ref') continue
      const entry = byWire.get(candidate.id) ?? { refs: [] }
      entry.refs.push(candidate)
      byWire.set(candidate.id, entry)
    }
    const shared = [...byWire.values()].find((entry) => entry.refs.length === 2)
    if (shared === undefined) throw new Error('the forward front has no two-ref shared wire')
    return shared.refs[0]!
  })
  const endPoint = await frontPoint(page, bind)
  const start = await blankPoint(page)
  await rightDrag(page, start, endPoint)
  await rightDrag(page, start, await blankPoint(page, 60, 60))

  await expect.poll(async () => (await counts(page)).wires)
    .toBe(before.wires + 1)
})

test('dragging an applied end into open space tears it off (parallel split)', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await addRef(page)
  await addAtom(page)
  await proveCurrent(page)
  const before = await counts(page)

  const atom = await page.evaluate(() => {
    const front = (window as DebugWindow).__vpaDebug!.proofFront('forward')
    const body = front.bodies.find((candidate) => candidate.kind === 'atom')
    if (body === undefined) throw new Error('the forward front has no atom body')
    return { x: body.x, y: body.y }
  })
  const at = await frontPoint(page, atom)
  const target = await blankPoint(page)
  await page.mouse.move(at.x, at.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y, { steps: 12 })
  await page.mouse.up()

  // The single-ended head wire splits into two side-by-side ends
  // (applyParallelSplit, wire-content.ts:173): the touched atom is deleted
  // and reborn twice, once per new wire — net +1 atom (2 new atoms, 1 old
  // one deleted). Its relation wire's pins transfer to one half and
  // duplicate onto the other (spec's "pin duplication is sound: ⊤ content
  // copies freely") — net +2 pin nodes (2 kept by transfer, 2 freshly
  // minted for the twin). Total: +3 nodes. The split relation wire becomes
  // two wires (net +1); the atom's own argument wire is shared by both new
  // atom copies via attachArgs, so no further wire is minted.
  await expect.poll(async () => (await counts(page)).nodes)
    .toBe(before.nodes + 3)
  await expect.poll(async () => (await counts(page)).wires)
    .toBe(before.wires + 1)
})

test('a closed right-stroke around one end wraps it in a cut', async ({ page, theoryFiles }) => {
  await openApp(page, theoryFiles)
  await addRef(page)
  await addAtom(page)
  await proveCurrent(page)
  const before = await counts(page)

  const atom = await page.evaluate(() => {
    const front = (window as DebugWindow).__vpaDebug!.proofFront('forward')
    const body = front.bodies.find((candidate) => candidate.kind === 'atom')
    if (body === undefined) throw new Error('the forward front has no atom body')
    return { x: body.x, y: body.y }
  })
  const at = await frontPoint(page, atom)
  const radius = 46
  await page.mouse.move(at.x - radius, at.y - radius)
  await page.mouse.down({ button: 'right' })
  for (const [dx, dy] of [
    [radius, -radius - 14],
    [radius + 20, 0],
    [radius, radius + 14],
    [-radius, radius + 14],
    [-radius - 20, 0],
    [-radius + 2, -radius + 3],
  ] as const) {
    await page.mouse.move(at.x + dx, at.y + dy, { steps: 4 })
  }
  await page.mouse.up({ button: 'right' })

  await expect.poll(async () => (await counts(page)).regions)
    .toBe(before.regions + 1)
})
