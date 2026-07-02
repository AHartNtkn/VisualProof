import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      view(): { scale: number; offsetX: number; offsetY: number }
      bodies(): { id: string; kind: string; x: number; y: number; r: number }[]
    }
  }
}

// The workspace folder picker (File System Access) can't be automated, so the
// e2e drives the honest single-file fallback — the same loadEntry road, no
// privileged path — by setting files on the real hidden #open-file-input. The
// file is a generated example emitted by the pree2e hook into examples/.
test('the app boots empty and opens a theory file on demand', async ({ page }) => {
  await page.goto('/?debug')
  await expect(page.locator('canvas')).toBeVisible()
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
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  const after = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(after).toBe(before + 1)
})

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  // build lhs: one identity node; snapshot as lhs (no citations, so this proves
  // against the empty boot context)
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  // set rhs = same diagram, prove with zero steps (met immediately)
  await page.getByRole('button', { name: /set goal rhs/i }).click()
  await page.getByRole('button', { name: /switch to prove/i }).click()
  await page.getByRole('button', { name: /assemble/i }).click()
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status).toMatch(/assembled|checked|adopted/i)
})

// The user's core interaction: nodes are draggable and STAY where dropped;
// the background is fixed (a drag on empty sheet space moves nothing).
test('a node drags under the cursor, the rearrangement persists, and the background never pans', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  await page.getByPlaceholder(/term, e\.g/).fill('\\y. y')
  await page.getByRole('button', { name: /add term/i }).click()
  // let the two-body layout settle so the grab point is current
  await page.waitForTimeout(500)

  const grab = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies()[0]!
    return { id: b.id, sx: b.x * v.scale + v.offsetX, sy: b.y * v.scale + v.offsetY }
  })
  const canvas = page.locator('canvas')
  const box = (await canvas.boundingBox())!
  // drag toward +x: the grabbed body must end up on the +x side of its sibling
  const target = { sx: grab.sx + 220, sy: grab.sy }
  await page.mouse.move(box.x + grab.sx, box.y + grab.sy)
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
  expect(Math.hypot(held.sx - target.sx, held.sy - target.sy)).toBeLessThan(25)
  await page.mouse.up()
  // after release the layout re-compacts (cohesion is a design force), but the
  // REARRANGEMENT persists: the dragged body settles on the side it was
  // dragged toward, relative to its sibling
  await page.waitForTimeout(900)
  const rel = await page.evaluate((id) => {
    const bs = window.__vpaDebug!.bodies()
    const a = bs.find((x) => x.id === id)!
    const o = bs.find((x) => x.id !== id)!
    return { dx: a.x - o.x, dist: Math.hypot(a.x - o.x, a.y - o.y) }
  }, grab.id)
  expect(rel.dx).toBeGreaterThan(0)
  expect(rel.dist).toBeGreaterThan(1)

  // background fixed: dragging from empty space changes no view offset and
  // moves no body
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
