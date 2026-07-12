import { test, expect } from '@playwright/test'

async function spawnTerm(page: import('@playwright/test').Page, source: string): Promise<void> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const count = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  const x = box.x + box.width * (0.38 + (count % 3) * 0.12)
  const y = box.y + box.height * (0.42 + (Math.floor(count / 3) % 2) * 0.14)
  await page.mouse.click(x, y, { button: 'right' })
  const menu = page.locator('.vpa-spawn-column')
  await menu.getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill(source)
  await input.press('Enter')
}

async function spawnRelation(page: import('@playwright/test').Page, defId: string): Promise<void> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  await page.mouse.click(box.x + box.width * 0.7, box.y + box.height * 0.65, { button: 'right' })
  const input = page.getByLabel('Search relations to spawn')
  await input.fill(defId)
  await input.press('Enter')
}

async function openMode(page: import('@playwright/test').Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
}

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      replay(): { mode: string; k: number; n: number; label: string; bodies: number }
      proof(): null | { kind: 'track'; direction: 'forward' | 'backward' } | { kind: 'dual'; side: 'forward' | 'backward' }
      companion(): { visible: boolean; label: string; bodies: number; rebuilds: number; pos: { id: string; x: number; y: number }[] } | null
      view(): { scale: number; offsetX: number; offsetY: number }
      bodies(): { id: string; kind: string; x: number; y: number; r: number; region: string }[]
      regions(): { id: string; kind: string; parent: string | null; x: number; y: number; r: number }[]
      wires(): { id: string; x: number; y: number }[]
      interaction(): { selected: readonly { kind: 'node' | 'region' | 'wire'; id: string }[]; pins: string[]; userZoom: number }
      theoryJson(): string
      editForm(): string
      fixed(): null | {
        ratio: number
        focused: 'forward' | 'backward'
        met: boolean
        forward: { cursor: number; rebuilds: number; view: { scale: number; offsetX: number; offsetY: number }; selected: number; pins: number; bodies: { id: string; kind: string; x: number; y: number; r: number }[]; regions: { id: string; kind: string; x: number; y: number; r: number }[]; motion: { playing: boolean; morph: string | null }; comprehension: { bubble: string } | null }
        backward: { cursor: number; rebuilds: number; view: { scale: number; offsetX: number; offsetY: number }; selected: number; pins: number; bodies: { id: string; kind: string; x: number; y: number; r: number }[]; regions: { id: string; kind: string; x: number; y: number; r: number }[]; motion: { playing: boolean; morph: string | null }; comprehension: { bubble: string } | null }
      }
      motion(): { playing: boolean; morph: string | null; ghosts: number; pulses: number; hover: number; preferences: { conversionAnimation: boolean; connectedMorph: boolean; speed: number; transitionGhosts: boolean; hoverEaseMs: number } }
      comprehension(): null | { bubble: string; cursor: number; historyLength: number; formalBoundary: string[]; materializedBoundary: string[]; externalWires: { draftWire: string; hostWire: string }[]; rect: { left: number; top: number; width: number; height: number }; draftBodies: { node: string; kind: string; x: number; y: number; point: { x: number; y: number } }[]; draftWires: { wire: string; point: { x: number; y: number } | null }[]; hostWires: { wire: string; point: { x: number; y: number } | null }[] }
      dispose(): void
    }
  }
}

// The workspace folder picker (File System Access) can't be automated, so the
// e2e drives the honest single-file fallback — the same loadEntry road, no
// privileged path — by setting files on the real hidden #open-file-input. The
// file is a generated example emitted by the pree2e hook into examples/.
test('the app boots empty and opens a theory file on demand', async ({ page }) => {
  await page.goto('/?debug')
  await expect(page.locator('#c')).toBeVisible()
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const lib = page.locator('#library')
  // Boot is empty: no built-in files, no theory content on screen.
  await expect(lib.getByRole('button', { name: 'Open folder…', exact: true })).toBeVisible()
  await expect(lib.getByRole('button', { name: 'Open file…', exact: true })).toBeVisible()
  await expect(lib).toContainText('No workspace folder open')
  await expect(lib).not.toContainText('plusAssoc')

  // Open a file through the real input, then expand its group — theorems appear.
  await page.locator('#open-file-input').setInputFiles('examples/frege.json')
  await expect(lib.getByRole('button', { name: 'Unload frege.json', exact: true })).toBeVisible()
  await lib.getByRole('button', { name: '▸ frege.json', exact: true }).click()
  await expect(lib).toContainText('plusAssoc')

  // Unloading removes the theory content again; the sheet is unaffected.
  await lib.getByRole('button', { name: 'Unload frege.json', exact: true }).click()
  await expect(lib).not.toContainText('plusAssoc')

  // still in EDIT mode throughout (the mode head in the status line)
  await expect(page.locator('#status')).toContainText('EDIT')
})

test('term entry adds a node to the edit diagram', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  const before = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  await spawnTerm(page, '\\x. x')
  const after = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(after).toBe(before + 1)
})

test('proof term spawning reuses the edit cascade, refuses open terms, and records closed-term introduction', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()

  const canvas = (await page.locator('#c').boundingBox())!
  const invoke = { x: canvas.x + canvas.width * 0.76, y: canvas.y + canvas.height * 0.72 }
  const before = await page.evaluate(() => ({
    ids: window.__vpaDebug!.bodies().map(({ id }) => id),
    nodeCount: window.__vpaDebug!.nodeCount(),
  }))
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })

  const cascade = page.locator('.vpa-spawn-column')
  await expect(cascade.getByRole('button', { name: 'λ term…', exact: true })).toBeVisible()
  await expect(cascade.locator('.vpa-spawn-bound-predicate')).toHaveCount(0)
  await expect(cascade.locator('.vpa-spawn-heading', { hasText: 'Namespaces' })).toHaveCount(0)
  await cascade.getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill('free')
  await input.press('Enter')
  await expect(cascade).toBeVisible()
  await expect(page.locator('.vpa-refusal')).toContainText("free ports ['free'] remain")
  await expect(page.locator('.vpa-temporal-copy')).toContainText('0 / 0')

  await input.fill('\\y. y')
  await input.press('Enter')
  await expect(cascade).toHaveCount(0)
  await expect(page.locator('.vpa-temporal-copy')).toContainText('1 / 1')
  const introduced = await page.evaluate((oldIds) => window.__vpaDebug!.bodies()
    .find((body) => body.kind === 'term' && !oldIds.includes(body.id)), before.ids)
  expect(introduced).toBeDefined()
  const view = await page.evaluate(() => window.__vpaDebug!.view())
  expect(Math.abs(introduced!.x * view.scale + view.offsetX - (invoke.x - canvas.x))).toBeLessThan(45)
  expect(Math.abs(introduced!.y * view.scale + view.offsetY - (invoke.y - canvas.y))).toBeLessThan(45)

  await page.keyboard.press('Control+z')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('0 / 1')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(before.nodeCount)
  await page.keyboard.press('Control+Shift+z')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('1 / 1')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(before.nodeCount + 1)
})

test('both fixed proof fronts share closed-term spawn policy, placement, refusal persistence, and disposal', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()?.focused)).toBe('forward')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()?.forward.motion.playing)).toBe(false)

  const invokeOn = async (side: 'forward' | 'backward') => {
    const front = page.locator(`.vpa-proof-front-${side} .vpa-proof-front-canvas`)
    const box = (await front.boundingBox())!
    const local = await page.evaluate(({ which, width, height }) => {
      const state = window.__vpaDebug!.fixed()![which]
      const candidates = [0.16, 0.3, 0.5, 0.7, 0.84].flatMap((x) =>
        [0.2, 0.38, 0.62, 0.8].map((y) => ({ x: width * x, y: height * y })))
      const clearance = (point: { x: number; y: number }) => Math.min(...state.bodies.map((body) => {
        const x = body.x * state.view.scale + state.view.offsetX
        const y = body.y * state.view.scale + state.view.offsetY
        return Math.hypot(point.x - x, point.y - y) - body.r
      }))
      return candidates.sort((a, b) => clearance(b) - clearance(a))[0]!
    }, { which: side, width: box.width, height: box.height })
    const invoke = { x: box.x + local.x, y: box.y + local.y }
    await front.click({ button: 'right', position: local })
    return { box, invoke }
  }

  const forwardBefore = await page.evaluate(() => window.__vpaDebug!.fixed()!.forward.bodies.map(({ id }) => id))
  const forwardInvocation = await invokeOn('forward')
  const cascade = page.locator('.vpa-spawn-column')
  await expect(cascade.getByRole('button', { name: 'λ term…', exact: true })).toBeVisible()
  await expect(cascade.locator('.vpa-spawn-bound-predicate')).toHaveCount(0)
  await expect(cascade.locator('.vpa-spawn-heading', { hasText: 'Namespaces' })).toHaveCount(0)
  await cascade.getByRole('button', { name: 'λ term…', exact: true }).click()
  const input = page.getByLabel('Lambda term to spawn')
  await input.fill('free')
  await input.press('Enter')
  await expect(cascade).toBeVisible()
  await expect(page.locator('.vpa-refusal')).toContainText("free ports ['free'] remain")
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(0)
  await input.fill('\\y. y')
  await input.press('Enter')

  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)
  const placedForward = await page.evaluate((oldIds) => {
    const front = window.__vpaDebug!.fixed()!.forward
    return {
      body: front.bodies.find((body) => body.kind === 'term' && !oldIds.includes(body.id)),
      view: front.view,
    }
  }, forwardBefore)
  expect(placedForward.body).toBeDefined()
  expect(Math.abs(
    placedForward.body!.x * placedForward.view.scale + placedForward.view.offsetX
      - (forwardInvocation.invoke.x - forwardInvocation.box.x),
  )).toBeLessThan(45)
  expect(Math.abs(
    placedForward.body!.y * placedForward.view.scale + placedForward.view.offsetY
      - (forwardInvocation.invoke.y - forwardInvocation.box.y),
  )).toBeLessThan(45)

  await invokeOn('backward')
  await cascade.getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\z. z')
  await page.getByLabel('Lambda term to spawn').press('Enter')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(1)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.bodies.filter((body) => body.kind === 'term').length)).toBe(2)

  await invokeOn('forward')
  await expect(cascade).toBeVisible()
  await page.evaluate(() => window.__vpaDebug!.dispose())
  await expect(cascade).toHaveCount(0)
  await expect(page.locator('.vpa-fixed-side-workspace')).toHaveCount(0)
})

test('ordinary proving is backward-first, forward is direct, and only fixed-side proving needs snapshots', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()

  const backward = page.getByRole('button', { name: 'Prove backward', exact: true })
  const forward = page.getByRole('button', { name: 'Prove forward', exact: true })
  const fixed = page.getByRole('button', { name: 'Prove fixed sides', exact: true })
  await expect(backward).toBeVisible()
  await expect(forward).toBeVisible()
  await expect(fixed).toBeVisible()

  await backward.click()
  await expect(page.locator('#status')).toContainText('[PROVE · BACKWARD]')
  expect(await page.evaluate(() => window.__vpaDebug!.proof())).toEqual({ kind: 'track', direction: 'backward' })
  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()

  await forward.click()
  await expect(page.locator('#status')).toContainText('[PROVE · FORWARD]')
  expect(await page.evaluate(() => window.__vpaDebug!.proof())).toEqual({ kind: 'track', direction: 'forward' })
  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()

  await fixed.click()
  await expect(page.locator('#status')).toContainText('[EDIT]')
  await expect(page.locator('.vpa-refusal')).toContainText('set both fixed sides before dual proving')
})

test('Compass production chrome overlays the canvas and exposes cursor history only while proving', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  const canvasBefore = await page.locator('#c').boundingBox()
  expect(canvasBefore).not.toBeNull()

  await expect(page.locator('.vpa-compass')).toBeVisible()
  await expect(page.locator('.vpa-temporal')).toBeHidden()
  await expect(page.locator('.vpa-row')).toHaveCount(0)

  await expect(page.getByRole('complementary', { name: 'Library' })).toBeVisible()
  expect(await page.locator('#c').boundingBox()).toEqual(canvasBefore)
  await page.getByRole('button', { name: 'Close library', exact: true }).click()

  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await expect(page.locator('.vpa-temporal')).toBeVisible()
  await expect(page.locator('.vpa-temporal-copy')).toHaveText('0 / 0 · start')
  await expect(page.locator('.vpa-temporal-redo')).toBeDisabled()
  expect(await page.locator('#c').boundingBox()).toEqual(canvasBefore)

  const at = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(at.x, at.y)
  await page.mouse.click(at.x, at.y, { button: 'right' })
  await page.locator('.vpa-proof-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true }).click()
  await expect(page.locator('.vpa-temporal-copy')).toContainText('1 / 1')
  await page.keyboard.press('Control+z')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('0 / 1')
  await expect(page.locator('.vpa-temporal-tick.is-future')).toHaveCount(1)
  const rail = (await page.locator('.vpa-temporal-rail').boundingBox())!
  await page.mouse.move(rail.x, rail.y + rail.height / 2)
  await page.mouse.down()
  await page.mouse.move(rail.x + rail.width, rail.y + rail.height / 2, { steps: 5 })
  await page.mouse.up()
  await expect(page.locator('.vpa-temporal-copy')).toContainText('1 / 1')
  await page.keyboard.press('Control+z')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('0 / 1')
  await page.keyboard.press('Control+Shift+z')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('1 / 1')

  await page.mouse.move(rail.x + rail.width * 0.5, rail.y + rail.height * 0.5)
  await expect(page.locator('.vpa-history-preview')).toBeVisible()
  await page.mouse.move(rail.x, rail.y - 30)
  await expect(page.locator('.vpa-history-preview')).toHaveCount(0)

  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await expect(page.locator('.vpa-temporal')).toBeHidden()
})

test('proof actions require right-click and forward/backward share direct labels and normalization', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '(\\x. x) y')
  const canvas = (await page.locator('#c').boundingBox())!
  const point = async () => page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })

  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  let at = await point()
  await page.mouse.click(canvas.x + at.x, canvas.y + at.y)
  await expect(page.locator('.vpa-proof-menu')).toHaveCount(0)
  await page.mouse.click(canvas.x + at.x, canvas.y + at.y, { button: 'right' })
  await expect(page.locator('.vpa-proof-menu')).toBeVisible()
  await expect(page.locator('.vpa-proof-menu')).toContainText('Wrap in a double cut')
  await expect(page.locator('.vpa-proof-menu')).toContainText('Normalize (also: double-click)')
  await expect(page.locator('.vpa-proof-menu')).not.toContainText('Un-')
  await page.keyboard.press('Escape')
  await page.mouse.dblclick(canvas.x + at.x, canvas.y + at.y)
  await expect(page.locator('#status')).toContainText('1 step(s)')

  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  at = await point()
  await page.mouse.click(canvas.x + at.x, canvas.y + at.y)
  await page.mouse.click(canvas.x + at.x, canvas.y + at.y, { button: 'right' })
  await expect(page.locator('.vpa-proof-menu')).toContainText('Wrap in a double cut')
  await expect(page.locator('.vpa-proof-menu')).toContainText('Normalize (also: double-click)')
  await expect(page.locator('.vpa-proof-menu')).not.toContainText('Un-')
})

test('Delete is a direct contextual proof gesture', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  const canvas = (await page.locator('#c').boundingBox())!
  const at = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(canvas.x + at.x, canvas.y + at.y)
  await page.keyboard.press('Delete')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('dragging a selected proof node into a legal region iterates it', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await spawnTerm(page, '\\y. y')
  const canvas = (await page.locator('#c').boundingBox())!
  const toPage = async (world: { x: number; y: number }) => {
    const view = await page.evaluate(() => window.__vpaDebug!.view())
    return { x: canvas.x + world.x * view.scale + view.offsetX, y: canvas.y + world.y * view.scale + view.offsetY }
  }
  const terms = await page.evaluate(() => window.__vpaDebug!.bodies().filter((body) => body.kind === 'term'))
  const wrappedAt = await toPage(terms[1]!)
  await page.mouse.click(wrappedAt.x, wrappedAt.y)
  await page.keyboard.press('w')
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()

  const outside = await page.evaluate(() => window.__vpaDebug!.bodies().find((body) => body.kind === 'term' && body.region === 'r0')!)
  const target = await page.evaluate(() => window.__vpaDebug!.regions().find((region) => region.kind === 'cut')!)
  const from = await toPage(outside)
  const to = await toPage(target)
  await page.mouse.click(from.x, from.y)
  await page.mouse.move(from.x, from.y)
  await page.mouse.down()
  await page.mouse.move(to.x, to.y, { steps: 12 })
  await page.mouse.up()

  await expect(page.locator('#status')).toContainText('1 step(s)')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(3)
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  // build lhs: one identity node; snapshot as lhs (no citations, so this proves
  // against the empty boot context)
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  // set rhs = same diagram, prove with zero steps (met immediately)
  await page.getByRole('button', { name: /set goal rhs/i }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()
  await page.locator('.vpa-fixed-side-declare').click()
  await page.getByRole('button', { name: 'Library', exact: true }).click()
  const sessionGroup = page.locator('#library').getByRole('button', { name: /Session \(adopted \+ defined\)/ })
  await sessionGroup.click()
  await expect(page.locator('#library')).toContainText('untitled')
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('fixed-side two-front workspace keeps both proof fronts live and independent', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  await expect(page.locator('.vpa-fixed-side-workspace')).toBeVisible()
  await expect(page.locator('.vpa-proof-front-canvas')).toHaveCount(2)
  await expect(page.locator('.vpa-fixed-side-seam')).toBeVisible()
  await expect(page.locator('#c')).toBeHidden()
  await expect(page.locator('#companion')).toBeHidden()
  await expect(page.getByRole('button', { name: /Side: .*toggle/ })).toHaveCount(0)

  const initial = await page.evaluate(() => window.__vpaDebug!.fixed()!)
  expect(initial.ratio).toBe(0.5)
  expect(initial.focused).toBe('forward')
  expect(initial.met).toBe(true)
  expect(initial.forward.cursor).toBe(0)
  expect(initial.backward.cursor).toBe(0)
  await expect(page.locator('.vpa-fixed-side-declare')).toBeEnabled()

  const clickFrontBody = async (side: 'forward' | 'backward', button: 'left' | 'right' = 'left') => {
    const canvas = page.locator(`.vpa-proof-front-${side} .vpa-proof-front-canvas`)
    const box = (await canvas.boundingBox())!
    const point = await page.evaluate((which) => {
      const front = window.__vpaDebug!.fixed()![which]
      const body = front.bodies.find((candidate) => candidate.kind === 'term')!
      return { x: body.x * front.view.scale + front.view.offsetX, y: body.y * front.view.scale + front.view.offsetY }
    }, side)
    await page.mouse.click(box.x + point.x, box.y + point.y, { button })
  }

  await clickFrontBody('backward')
  const backwardCanvas = (await page.locator('.vpa-proof-front-backward .vpa-proof-front-canvas').boundingBox())!
  await page.mouse.move(backwardCanvas.x + backwardCanvas.width / 2, backwardCanvas.y + backwardCanvas.height / 2)
  await page.mouse.wheel(0, -220)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.view.scale)).toBeGreaterThan(initial.backward.view.scale)
  const preparedBackward = await page.evaluate(() => window.__vpaDebug!.fixed()!.backward)

  await clickFrontBody('forward')
  await clickFrontBody('forward', 'right')
  await page.locator('.vpa-proof-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)
  const afterForward = await page.evaluate(() => window.__vpaDebug!.fixed()!)
  expect(afterForward.backward.cursor).toBe(0)
  expect(afterForward.backward.rebuilds).toBe(initial.backward.rebuilds)
  expect(afterForward.backward.selected).toBe(1)
  expect(afterForward.backward.view).toEqual(preparedBackward.view)
  expect(afterForward.met).toBe(false)
  await expect(page.locator('.vpa-fixed-side-declare')).toBeDisabled()

  await clickFrontBody('backward', 'right')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.focused)).toBe('backward')
  await expect(page.locator('.vpa-temporal-copy')).toContainText('backward')
  await page.locator('.vpa-proof-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(1)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.met)).toBe(true)
  await expect(page.locator('.vpa-fixed-side-declare')).toBeEnabled()

  const seam = (await page.locator('.vpa-fixed-side-seam').boundingBox())!
  const workspace = (await page.locator('.vpa-fixed-side-workspace').boundingBox())!
  const seamY = seam.y + seam.height * 0.7
  await page.mouse.move(seam.x + seam.width / 2, seamY)
  await page.mouse.down()
  await page.mouse.move(workspace.x + workspace.width * 0.9, seamY)
  await page.mouse.up()
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.ratio)).toBe(0.7)
  await page.locator('.vpa-fixed-side-seam').dblclick({ position: { x: 4, y: seam.height * 0.7 } })
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.ratio)).toBe(0.5)

  const beforeOverlay = await Promise.all([
    page.locator('.vpa-proof-front-forward').boundingBox(),
    page.locator('.vpa-proof-front-backward').boundingBox(),
  ])
  await page.getByRole('button', { name: 'Library', exact: true }).click()
  await expect(page.getByRole('complementary', { name: 'Library' })).toBeVisible()
  expect(await Promise.all([
    page.locator('.vpa-proof-front-forward').boundingBox(),
    page.locator('.vpa-proof-front-backward').boundingBox(),
  ])).toEqual(beforeOverlay)
  await page.getByRole('button', { name: 'Close library', exact: true }).click()

  await page.setViewportSize({ width: 600, height: 720 })
  await expect(page.locator('.vpa-fixed-side-too-narrow')).toBeVisible()
  await expect(page.locator('.vpa-fixed-side-too-narrow')).toContainText('at least 648px')
  await page.setViewportSize({ width: 1280, height: 720 })
  await expect(page.locator('.vpa-fixed-side-too-narrow')).toBeHidden()

  await page.getByRole('button', { name: /Mode: Prove/ }).click()
  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await expect(page.locator('.vpa-fixed-side-workspace')).toHaveCount(0)
  await expect(page.locator('#c')).toBeVisible()
  expect(await page.evaluate(() => window.__vpaDebug!.fixed())).toBeNull()
})

test('fixed-side motion guard defers one front and blocks shared-session mutation on the other', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '(\\x. x) y')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  const point = async (side: 'forward' | 'backward') => {
    const canvas = (await page.locator(`.vpa-proof-front-${side} canvas`).boundingBox())!
    const local = await page.evaluate((which) => {
      const front = window.__vpaDebug!.fixed()![which]
      const body = front.bodies.find((candidate) => candidate.kind === 'term')!
      return { x: body.x * front.view.scale + front.view.offsetX, y: body.y * front.view.scale + front.view.offsetY }
    }, side)
    return { x: canvas.x + local.x, y: canvas.y + local.y }
  }

  const forward = await point('forward')
  await page.mouse.dblclick(forward.x, forward.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.motion.playing)).toBe(true)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(0)

  const backward = await point('backward')
  await page.mouse.dblclick(backward.x, backward.y)
  await page.keyboard.press('Control+z')
  await page.waitForTimeout(80)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.motion.playing)).toBe(false)

  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor), { timeout: 2000 }).toBe(1)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)
})

test('production motion layers defer conversion and expose the five approved controls', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '(\\x. x) y')
  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  const canvas = (await page.locator('#c').boundingBox())!
  const point = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.dblclick(canvas.x + point.x, canvas.y + point.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.motion().playing)).toBe(true)
  await expect(page.locator('#status')).toContainText('0 step(s)')
  await page.keyboard.press('Control+z')
  await page.waitForTimeout(80)
  await expect(page.locator('#status')).toContainText('0 step(s)')
  await expect.poll(() => page.locator('#status').textContent(), { timeout: 2000 }).toContain('1 step(s)')
  expect(await page.evaluate(() => window.__vpaDebug!.motion().playing)).toBe(false)

  await page.getByRole('button', { name: 'Utilities', exact: true }).click()
  await expect(page.locator('.vpa-motion-conversion')).toBeChecked()
  await expect(page.locator('.vpa-motion-connected')).toBeChecked()
  await expect(page.locator('.vpa-motion-ghosts')).toBeChecked()
  await expect(page.locator('.vpa-motion-hover')).toBeChecked()
  await expect(page.locator('.vpa-motion-speed')).toHaveValue('1')
  await page.locator('.vpa-motion-connected').uncheck()
  await page.locator('.vpa-motion-speed').fill('3')
  await expect(page.locator('.vpa-motion-speed-value')).toHaveText('3×')
  expect(await page.evaluate(() => window.__vpaDebug!.motion().preferences.connectedMorph)).toBe(false)
  expect(await page.evaluate(() => window.__vpaDebug!.motion().preferences.speed)).toBe(3)
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('anonymous comprehension opens from the real proof menu, cancels exactly, and commits one step', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  const canvas = (await page.locator('#c').boundingBox())!
  const term = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(canvas.x + term.x, canvas.y + term.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('2')
  await page.getByLabel('Bubble arity').press('Enter')
  const bubblePoint = async () => page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const bubble = window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!
    return { x: bubble.x * view.scale + view.offsetX, y: bubble.y * view.scale + view.offsetY, r: bubble.r * view.scale }
  })
  let bubble = await bubblePoint()
  await page.mouse.click(canvas.x + bubble.x + bubble.r * 0.55, canvas.y + bubble.y, { button: 'right' })
  await page.locator('.vpa-spawn-bound-predicate').click()
  bubble = await bubblePoint()
  await page.mouse.click(canvas.x + bubble.x + bubble.r * 0.88, canvas.y + bubble.y)
  await page.keyboard.press('w')
  await page.mouse.click(canvas.x + canvas.width * 0.16, canvas.y + canvas.height * 0.78, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\z. z')
  await page.getByLabel('Lambda term to spawn').press('Enter')

  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  bubble = await bubblePoint()
  const invoke = { x: canvas.x + bubble.x + bubble.r * 0.88, y: canvas.y + bubble.y }
  await page.mouse.click(invoke.x, invoke.y)
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await expect(page.locator('.vpa-comprehension-editor')).toBeVisible()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.formalBoundary.length)).toBe(2)
  const editorCanvas = page.locator('.vpa-comprehension-canvas')
  const editorBox = (await editorCanvas.boundingBox())!
  await page.mouse.click(editorBox.x + editorBox.width * 0.55, editorBox.y + editorBox.height * 0.55, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\u. u')
  await page.getByLabel('Lambda term to spawn').press('Enter')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.historyLength)).toBe(2)
  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.cursor)).toBe(0)
  await page.keyboard.press('Control+Shift+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.cursor)).toBe(1)

  const editorBeforeSecond = (await editorCanvas.boundingBox())!
  await page.mouse.click(editorBeforeSecond.x + editorBeforeSecond.width * 0.72, editorBeforeSecond.y + editorBeforeSecond.height * 0.62, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\v. v')
  await page.getByLabel('Lambda term to spawn').press('Enter')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.draftBodies
    .filter((body) => body.kind === 'term').length)).toBe(2)
  const looseDraftWires = await page.evaluate(() => window.__vpaDebug!.comprehension()!.draftWires
    .filter((wire) => !wire.wire.startsWith('arg') && wire.point !== null))
  expect(looseDraftWires).toHaveLength(2)
  await page.mouse.move(looseDraftWires[0]!.point!.x, looseDraftWires[0]!.point!.y)
  await page.mouse.down()
  await page.mouse.move(looseDraftWires[1]!.point!.x, looseDraftWires[1]!.point!.y, { steps: 4 })
  const liveTarget = await page.evaluate((wire) => window.__vpaDebug!.comprehension()!.draftWires
    .find((candidate) => candidate.wire === wire)!.point!, looseDraftWires[1]!.wire)
  await page.mouse.move(liveTarget.x, liveTarget.y, { steps: 4 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()!.draftWires
    .filter((wire) => !wire.wire.startsWith('arg')).length)).toBe(1)
  await page.waitForTimeout(250)
  const draftBodies = await page.evaluate(() => window.__vpaDebug!.comprehension()!.draftBodies
    .filter((body) => body.kind === 'term'))
  const held = draftBodies[0]!
  const neighbour = draftBodies[1]!
  await page.mouse.click(held.point.x, held.point.y)
  const neighbourBefore = await page.evaluate((node) => window.__vpaDebug!.comprehension()!.draftBodies.find((body) => body.node === node)!, neighbour.node)
  await page.mouse.move(held.point.x, held.point.y)
  await page.mouse.down()
  await page.mouse.move(neighbour.point.x, neighbour.point.y)
  const heldDuring = await page.evaluate((node) => window.__vpaDebug!.comprehension()!.draftBodies.find((body) => body.node === node)!, held.node)
  await page.waitForTimeout(450)
  const liveBodies = await page.evaluate(({ held, neighbour }) => ({
    held: window.__vpaDebug!.comprehension()!.draftBodies.find((body) => body.node === held)!,
    neighbour: window.__vpaDebug!.comprehension()!.draftBodies.find((body) => body.node === neighbour)!,
  }), { held: held.node, neighbour: neighbour.node })
  expect(Math.hypot(liveBodies.held.x - heldDuring.x, liveBodies.held.y - heldDuring.y)).toBeLessThan(0.01)
  expect(Math.hypot(liveBodies.neighbour.x - neighbourBefore.x, liveBodies.neighbour.y - neighbourBefore.y)).toBeGreaterThan(0.01)
  await page.mouse.up()

  const title = (await page.locator('.vpa-comprehension-title').boundingBox())!
  await page.mouse.move(title.x + title.width * 0.35, title.y + title.height / 2)
  await page.mouse.down()
  await page.mouse.move(canvas.x + canvas.width - 260, canvas.y + 80, { steps: 8 })
  await page.mouse.up()

  const points = await page.evaluate(() => {
    const debug = window.__vpaDebug!
    const state = debug.comprehension()!
    const rootWires = new Set(debug.diagram().wires.filter((wire) => wire.scope === 'r0').map((wire) => wire.id))
    return {
      host: state.hostWires.find((wire) => rootWires.has(wire.wire) && wire.point !== null)!,
      arg1: state.draftWires.find((wire) => wire.wire === 'arg1')!,
    }
  })
  expect(points.host.point).not.toBeNull()
  expect(points.arg1.point).not.toBeNull()
  await page.mouse.move(points.host.point!.x, points.host.point!.y)
  await page.mouse.down()
  await page.mouse.move(points.arg1.point!.x, points.arg1.point!.y, { steps: 8 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.externalWires.length)).toBe(1)
  const reused = await page.evaluate((hostWire) => {
    const state = window.__vpaDebug!.comprehension()!
    return {
      host: state.hostWires.find((wire) => wire.wire === hostWire)!,
      arg2: state.draftWires.find((wire) => wire.wire === 'arg2')!,
    }
  }, points.host.wire)
  await page.mouse.move(reused.host.point!.x, reused.host.point!.y)
  await page.mouse.down()
  await page.mouse.move(reused.arg2.point!.x, reused.arg2.point!.y, { steps: 8 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.formalBoundary)).toEqual(['arg1', 'arg1'])
  expect(await page.evaluate(() => window.__vpaDebug!.comprehension()?.externalWires.length)).toBe(1)
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect(page.locator('.vpa-comprehension-editor')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('0 step(s)')

  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await page.getByRole('button', { name: 'Instantiate', exact: true }).click()
  await expect(page.locator('.vpa-comprehension-editor')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('anonymous comprehension uses the same transaction in backward proving', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  const canvas = (await page.locator('#c').boundingBox())!
  const term = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(canvas.x + term.x, canvas.y + term.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('1')
  await page.getByLabel('Bubble arity').press('Enter')
  const bubblePoint = async () => page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const bubble = window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!
    return { x: bubble.x * view.scale + view.offsetX, y: bubble.y * view.scale + view.offsetY, r: bubble.r * view.scale }
  })
  let bubble = await bubblePoint()
  await page.mouse.click(canvas.x + bubble.x + bubble.r * 0.55, canvas.y + bubble.y, { button: 'right' })
  await page.locator('.vpa-spawn-bound-predicate').click()

  await openMode(page)
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  bubble = await bubblePoint()
  const invoke = { x: canvas.x + bubble.x + bubble.r * 0.88, y: canvas.y + bubble.y }
  await page.mouse.click(invoke.x, invoke.y)
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.comprehension()?.formalBoundary)).toEqual(['arg1'])
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect(page.locator('#status')).toContainText('0 step(s)')

  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await page.getByRole('button', { name: 'Instantiate', exact: true }).click()
  await expect(page.locator('#status')).toContainText('1 step(s)')
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('fixed-side anonymous comprehension guards the shared session and advances only its owning front', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  const canvas = (await page.locator('#c').boundingBox())!
  const term = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(canvas.x + term.x, canvas.y + term.y)
  await page.keyboard.press('Shift+w')
  await page.getByLabel('Bubble arity').fill('1')
  await page.getByLabel('Bubble arity').press('Enter')
  const bubbleAt = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const bubble = window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!
    return { x: bubble.x * view.scale + view.offsetX, y: bubble.y * view.scale + view.offsetY, r: bubble.r * view.scale }
  })
  await page.mouse.click(canvas.x + bubbleAt.x + bubbleAt.r * 0.55, canvas.y + bubbleAt.y, { button: 'right' })
  await page.locator('.vpa-spawn-bound-predicate').click()
  const wrappedAt = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const bubble = window.__vpaDebug!.regions().find((region) => region.kind === 'bubble')!
    return { x: bubble.x * view.scale + view.offsetX, y: bubble.y * view.scale + view.offsetY, r: bubble.r * view.scale }
  })
  await page.mouse.click(canvas.x + wrappedAt.x + wrappedAt.r * 0.88, canvas.y + wrappedAt.y)
  await page.keyboard.press('w')
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  const cutAt = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const cut = window.__vpaDebug!.regions().find((region) => region.kind === 'cut')!
    return { x: cut.x * view.scale + view.offsetX, y: cut.y * view.scale + view.offsetY, r: cut.r * view.scale }
  })
  await page.mouse.click(canvas.x + cutAt.x + cutAt.r * 0.92, canvas.y + cutAt.y)
  await page.keyboard.press('Delete')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.regions().some((region) => region.kind === 'cut'))).toBe(false)
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  const forwardCanvas = page.locator('.vpa-proof-front-forward canvas')
  const box = (await forwardCanvas.boundingBox())!
  const point = await page.evaluate(() => {
    const front = window.__vpaDebug!.fixed()!.forward
    const bubble = front.regions.find((region) => region.kind === 'bubble')!
    return { x: bubble.x * front.view.scale + front.view.offsetX, y: bubble.y * front.view.scale + front.view.offsetY, r: bubble.r * front.view.scale }
  })
  const invoke = { x: box.x + point.x + point.r * 0.88, y: box.y + point.y }
  await page.mouse.click(invoke.x, invoke.y)
  await page.mouse.click(invoke.x, invoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.comprehension !== null)).toBe(true)
  await page.keyboard.press('Control+z')
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)
  await page.getByRole('button', { name: 'Instantiate', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)

  const backwardCanvas = page.locator('.vpa-proof-front-backward canvas')
  const backwardBox = (await backwardCanvas.boundingBox())!
  const backwardPoint = await page.evaluate(() => {
    const front = window.__vpaDebug!.fixed()!.backward
    const bubble = front.regions.find((region) => region.kind === 'bubble')!
    return { x: bubble.x * front.view.scale + front.view.offsetX, y: bubble.y * front.view.scale + front.view.offsetY, r: bubble.r * front.view.scale }
  })
  const backwardInvoke = { x: backwardBox.x + backwardPoint.x + backwardPoint.r * 0.88, y: backwardBox.y + backwardPoint.y }
  await page.mouse.click(backwardInvoke.x, backwardInvoke.y)
  await page.mouse.click(backwardInvoke.x, backwardInvoke.y, { button: 'right' })
  await page.getByRole('button', { name: 'New relation…', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.comprehension !== null)).toBe(true)
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.comprehension)).toBeNull()
  expect(await page.evaluate(() => window.__vpaDebug!.fixed()!.backward.cursor)).toBe(0)
})

// The plan-14 deliverable: a relational theorem replays step-by-step through the
// live shell (enterReplay + gotoReplayStep + carryOver + boundary rendering), not
// just through the headless mkReplay unit. Drives plusComm — the const-free
// relational derivation — from the real Library "▶ Replay" button.
test('a relational theorem replays step by step through the live shell', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const lib = page.locator('#library')
  await page.locator('#open-file-input').setInputFiles('examples/frege.json')
  await lib.getByRole('button', { name: '▸ frege.json', exact: true }).click()
  await expect(lib).toContainText('plusComm')

  // The Library renders one "▶ Replay" button per theorem in derivation
  // (dependency) order, so plusComm — which cites succShiftS — is last.
  await lib.getByRole('button', { name: '▶ Replay', exact: true }).last().click()

  // Entered replay at step 0 (the lhs). plusComm is a large derivation — the
  // n>=40 floor confirms we grabbed a substantial theorem (not a 5-11 step one),
  // catching any drift in the theorem order behind the index-4 button.
  const start = await page.evaluate(() => window.__vpaDebug!.replay())
  expect(start.mode).toBe('replay')
  expect(start.k).toBe(0)
  expect(start.n).toBeGreaterThanOrEqual(40)
  expect(start.bodies).toBeGreaterThan(0)
  await expect(page.locator('.vpa-temporal')).toBeVisible()
  const lhsNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())

  // Replay is diagram-read-only, not physics-frozen: Ctrl remains the global
  // layout handle while ordinary/Shift gestures cannot create a selection.
  await page.waitForTimeout(500)
  const replayGrab = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'ref' || candidate.kind === 'term')!
    return { id: body.id, x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  const replayBox = (await page.locator('#c').boundingBox())!
  const replayTarget = { x: replayGrab.x + 8, y: replayGrab.y + 28 }
  await page.mouse.move(replayBox.x + replayGrab.x, replayBox.y + replayGrab.y)
  await page.keyboard.down('Control')
  await page.mouse.down()
  await page.mouse.move(replayBox.x + replayTarget.x, replayBox.y + replayTarget.y, { steps: 8 })
  await page.keyboard.up('Control')
  await page.mouse.up()
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.interaction().pins)).toContain(replayGrab.id)
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([])

  // The companion pane shows the theorem's final state (the goal) while stepping.
  await expect.poll(async () => (await page.evaluate(() => window.__vpaDebug!.companion()))?.bodies ?? 0).toBeGreaterThan(0)
  const compStart = await page.evaluate(() => window.__vpaDebug!.companion())
  expect(compStart!.visible).toBe(true)
  expect(compStart!.label).toBe('goal: final state')

  // Arrow-key stepping advances the step and rebuilds the displayed diagram: by
  // step 20 the derivation has unfolded the relations, so the diagram carries
  // strictly more nodes than the lhs and the step label is a real rule name.
  for (let i = 0; i < 20; i++) await page.keyboard.press('ArrowRight')
  const mid = await page.evaluate(() => window.__vpaDebug!.replay())
  expect(mid.k).toBe(20)
  expect(mid.label.length).toBeGreaterThan(0)
  const midNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(midNodes).toBeGreaterThan(lhsNodes)

  // Stepping the replay does not change what the companion targets: it still
  // shows the final state (identity-stable diagram, no reseed) with the same
  // body count as at step 0.
  const compMid = await page.evaluate(() => window.__vpaDebug!.companion())
  expect(compMid!.label).toBe('goal: final state')
  expect(compMid!.bodies).toBe(compStart!.bodies)
  // 20 replay steps rebuilt the MAIN diagram 20 times; the companion target (the
  // final state) is identity-stable, so the companion engine was never reseeded.
  expect(compMid!.rebuilds).toBe(compStart!.rebuilds)

  // The shared temporal rail drives the same replay cursor (carryOver path).
  await page.locator('.vpa-temporal-redo').click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(21)
  await page.locator('.vpa-temporal-undo').click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(20)

  // Exiting replay returns to EDIT mode with the sheet restored.
  await page.getByRole('button', { name: /Mode: Replay/ }).click()
  await page.getByRole('button', { name: 'Exit replay', exact: true }).click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().mode)).toBe('edit')
  await expect(page.locator('#status')).toContainText('EDIT')
})

// Plan 15: name a live selection as a relation, then exercise every downstream
// consequence — the Session group lists it, relFold cites it, Save serializes it,
// and a reload round-trips it. Real canvas clicks throughout; the debug seam is a
// pure locator (bodies() for nodes, wires() for verified-hittable wire points).
test('name a selection as a relation, fold with it, save it, and round-trip on reload', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  const canvas = page.locator('#c')
  const box = (await canvas.boundingBox())!
  // Read geometry and camera in ONE evaluate so a still-settling layout can't
  // skew the world→screen mapping between the two reads.
  const clickTerm = async (): Promise<void> => {
    const s = await page.evaluate(() => {
      const v = window.__vpaDebug!.view()
      const b = window.__vpaDebug!.bodies().find((x) => x.kind === 'term')!
      return { x: b.x * v.scale + v.offsetX, y: b.y * v.scale + v.offsetY }
    })
    await page.mouse.click(box.x + s.x, box.y + s.y)
  }
  // A guaranteed-empty click (far corner, off every node/wire and below the top
  // chrome) clears the current selection — the sheet region is never a hit.
  const clickEmpty = async (): Promise<void> => {
    await page.mouse.click(box.x + box.width - 2, box.y + box.height - 2)
  }

  // A closed lambda has only an output line, so the whole-node selection has a
  // single crossing wire → an arity-1 relation.
  await spawnTerm(page, '\\x. x')
  await page.waitForTimeout(400) // let the layout settle so seam coords are current

  // Select the term node (click its body), then the EDIT menu offers Define.
  await clickTerm()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([
    expect.objectContaining({ kind: 'node' }),
  ])
  // Structural fingerprint of the sheet BEFORE defining: a conservative
  // definitional extension must leave it byte-identical (not just node-count).
  const sheetBefore = await page.evaluate(() => window.__vpaDebug!.editForm())
  expect(sheetBefore.length).toBeGreaterThan(0) // a real fingerprint, not a vacuous empty string
  const selectedTerm = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: b.x * v.scale + v.offsetX, y: b.y * v.scale + v.offsetY }
  })
  await page.mouse.click(box.x + selectedTerm.x, box.y + selectedTerm.y, { button: 'right' })
  await page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true }).click()
  await expect(page.locator('.vpa-action-instruction')).toContainText('canonical order')

  // No wire picking needed: name it in the DEDICATED field and commit with the
  // canonical argument order. (Picking crossing wires remains an override.)
  await page.locator('#relation-name').fill('logic/R')
  await page.locator('#action-menu').getByRole('button', { name: /Commit relation definition \(canonical argument order\)/ }).click()
  // The whole define flow (defineRelation + defineEntry) changed nothing on the
  // sheet — the canonical form is identical to the pre-define snapshot.
  expect(await page.evaluate(() => window.__vpaDebug!.editForm())).toBe(sheetBefore)

  // The Session group lists the new relation beside adopted theorems.
  const lib = page.locator('#library')
  await lib.getByRole('button', { name: /Session/, exact: false }).click()
  await expect(lib).toContainText('relations: logic/R')

  // Folding is a CONSTRUCTION operation — no goals, no PROVE — and the
  // argument wires are INFERRED by occurrence matching: choose the relation,
  // done. No text box, no wire picking.
  await clickEmpty()
  await clickTerm()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([
    expect.objectContaining({ kind: 'node' }),
  ])
  const foldTerm = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: b.x * v.scale + v.offsetX, y: b.y * v.scale + v.offsetY }
  })
  await page.mouse.click(box.x + foldTerm.x, box.y + foldTerm.y, { button: 'right' })
  await page.locator('#action-menu').getByRole('button', { name: 'Fold into a relation…', exact: true }).click()
  await page.locator('#action-menu').getByRole('button', { name: "Fold into 'logic/R'", exact: true }).click()
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).some((b) => b.kind === 'ref'))
    .toBe(true)

  // The contextual cascade searches the live relation library and drops a
  // fresh qualified relation reference at the invocation point with bare argument wires.
  const refsBefore = await page.evaluate(() => window.__vpaDebug!.bodies().filter((b) => b.kind === 'ref').length)
  await spawnRelation(page, 'logic/R')
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).filter((b) => b.kind === 'ref').length)
    .toBe(refsBefore + 1)

  // Unfolding is construction too: select the spawned ref, Unfold — the body
  // (one \x. x node) replaces it.
  await page.waitForTimeout(600)
  const termsBefore = await page.evaluate(() => window.__vpaDebug!.bodies().filter((b) => b.kind === 'term').length)
  const refPos = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const refs = window.__vpaDebug!.bodies().filter((b) => b.kind === 'ref')
    const r = refs[refs.length - 1]!
    return { id: r.id, x: r.x * v.scale + v.offsetX, y: r.y * v.scale + v.offsetY }
  })
  await page.mouse.click(box.x + refPos.x, box.y + refPos.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([{ kind: 'node', id: refPos.id }])
  await page.mouse.click(box.x + refPos.x, box.y + refPos.y, { button: 'right' })
  await page.locator('#action-menu').getByRole('button', { name: 'Unfold relation', exact: true }).click()
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).filter((b) => b.kind === 'term').length)
    .toBe(termsBefore + 1)

  // Save serializes the relation. Capture the live theory JSON (the same object
  // Save theory writes) and confirm it carries the exact qualified id.
  const json = await page.evaluate(() => window.__vpaDebug!.theoryJson())
  const theory = JSON.parse(json) as { relations: Record<string, unknown> }
  expect(theory.relations['logic/R']).toBeDefined()

  // Reload round-trip: a FRESH empty app loads the saved JSON through the real
  // #open-file-input; the loaded group lists the qualified relation again.
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#open-file-input').setInputFiles({ name: 'saved.json', mimeType: 'application/json', buffer: Buffer.from(json) })
  const lib2 = page.locator('#library')
  await expect(lib2.getByRole('button', { name: 'Unload saved.json', exact: true })).toBeVisible()
  await lib2.getByRole('button', { name: '▸ saved.json', exact: true }).click()
  await expect(lib2).toContainText('relations: logic/R')
})

// Physics is an explicit Ctrl gesture. Releasing Ctrl before pointer-up pins a
// node where it was dropped; plain empty-space dragging never pans the frame.
test('a Ctrl-drag follows the cursor, release order pins it, and the background never pans', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x')
  await spawnTerm(page, '\\y. y')
  // let the two-body layout settle so the grab point is current
  await page.waitForTimeout(500)

  const grab = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const terms = window.__vpaDebug!.bodies()
      .filter((b) => b.kind === 'term')
      .map((b) => ({ id: b.id, x: b.x, y: b.y, sx: b.x * v.scale + v.offsetX, sy: b.y * v.scale + v.offsetY }))
      .sort((a, b) => a.x - b.x)
    const left = terms[0]!
    const right = terms[terms.length - 1]!
    return { ...right, target: { sx: left.sx + 6, sy: right.sy }, dir: -1 }
  })
  const canvas = page.locator('#c')
  const box = (await canvas.boundingBox())!
  // Drag inward, inside the fixed frame's hard wall. An outward fixed-pixel
  // target can legitimately clamp at the border instead of staying under the
  // cursor, which is frame behavior rather than drag failure.
  const target = grab.target
  await page.mouse.move(box.x + grab.sx, box.y + grab.sy)
  await page.keyboard.down('Control')
  await page.mouse.down()
  // several intermediate moves: the drag engages after the click slop
  for (let i = 1; i <= 8; i++) {
    await page.mouse.move(box.x + grab.sx + (target.sx - grab.sx) * (i / 8), box.y + grab.sy + (target.sy - grab.sy) * (i / 8))
    await page.waitForTimeout(30)
  }
  // mid-drag: the body is pinned under the cursor (this is the drag WORKING)
  await page.waitForTimeout(120)
  const held = await page.evaluate((id) => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies().find((x) => x.id === id)!
    return { sx: b.x * v.scale + v.offsetX, sy: b.y * v.scale + v.offsetY }
  }, grab.id)
  expect(Math.hypot(held.sx - target.sx, held.sy - target.sy)).toBeLessThan(30)
  await page.keyboard.up('Control')
  await page.mouse.up()
  await expect.poll(async () => page.evaluate(() => window.__vpaDebug!.interaction().pins)).toContain(grab.id)
  // The moved node is now an explicit solver constraint. Wait for the remaining
  // bodies to settle before checking the durable rearrangement.
  await page.waitForFunction(() => {
    const w = window as unknown as { __lastBodies?: string; __stable?: number }
    const now = JSON.stringify(window.__vpaDebug!.bodies().map((b) => [Math.round(b.x * 5), Math.round(b.y * 5)]))
    w.__stable = now === w.__lastBodies ? (w.__stable ?? 0) + 1 : 0
    w.__lastBodies = now
    return (w.__stable ?? 0) >= 3
  }, undefined, { polling: 250, timeout: 30000 })
  const rel = await page.evaluate(({ id, startX, dir }) => {
    const bs = window.__vpaDebug!.bodies()
    const a = bs.find((x) => x.id === id)!
    const o = bs.find((x) => x.id !== id)!
    return { moved: (a.x - startX) * dir, dist: Math.hypot(a.x - o.x, a.y - o.y) }
  }, { id: grab.id, startX: grab.x, dir: grab.dir })
  expect(rel.moved).toBeGreaterThan(5)
  expect(rel.dist).toBeGreaterThan(1)

  // background fixed: dragging from empty space changes no view offset and
  // moves no body
  // rest again before the no-pan check (the release above may still be settling)
  await page.waitForFunction(() => {
    const w = window as unknown as { __lastBodies2?: string; __stable2?: number }
    const now = JSON.stringify(window.__vpaDebug!.bodies().map((b) => [Math.round(b.x * 5), Math.round(b.y * 5)]))
    w.__stable2 = now === w.__lastBodies2 ? (w.__stable2 ?? 0) + 1 : 0
    w.__lastBodies2 = now
    return (w.__stable2 ?? 0) >= 3
  }, undefined, { polling: 250, timeout: 30000 })
  const before = await page.evaluate(() => ({ v: window.__vpaDebug!.view(), bs: window.__vpaDebug!.bodies() }))
  await page.mouse.move(box.x + box.width - 60, box.y + box.height - 60)
  await page.mouse.down()
  await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2, { steps: 6 })
  await page.mouse.up()
  await page.waitForTimeout(200)
  const afterPan = await page.evaluate(() => ({ v: window.__vpaDebug!.view(), bs: window.__vpaDebug!.bodies() }))
  // the camera is a pure fit of the (resting) content — an empty-space drag
  // leaves it where it was, up to rest micro-jitter
  expect(Math.abs(afterPan.v.scale - before.v.scale)).toBeLessThan(0.01)
  expect(Math.abs(afterPan.v.offsetX - before.v.offsetX)).toBeLessThan(1)
  expect(Math.abs(afterPan.v.offsetY - before.v.offsetY)).toBeLessThan(1)
  for (const b of before.bs) {
    const nb = afterPan.bs.find((x) => x.id === b.id)!
    expect(Math.hypot(nb.x - b.x, nb.y - b.y)).toBeLessThan(2)
  }
})
