import { test, expect } from '@playwright/test'

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      replay(): { mode: string; k: number; n: number; label: string; bodies: number }
      view(): { scale: number; offsetX: number; offsetY: number }
      bodies(): { id: string; kind: string; x: number; y: number; r: number }[]
      wires(): { id: string; x: number; y: number }[]
      theoryJson(): string
      editForm(): string
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
  const lhsNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())

  // Arrow-key stepping advances the step and rebuilds the displayed diagram: by
  // step 20 the derivation has unfolded the relations, so the diagram carries
  // strictly more nodes than the lhs and the step label is a real rule name.
  for (let i = 0; i < 20; i++) await page.keyboard.press('ArrowRight')
  const mid = await page.evaluate(() => window.__vpaDebug!.replay())
  expect(mid.k).toBe(20)
  expect(mid.label.length).toBeGreaterThan(0)
  const midNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  expect(midNodes).toBeGreaterThan(lhsNodes)

  // The menu Prev/Next buttons drive the same stepper (carryOver path).
  await page.getByRole('button', { name: 'Next ▶', exact: true }).click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(21)
  await page.getByRole('button', { name: '◀ Prev', exact: true }).click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(20)

  // Exiting replay returns to EDIT mode with the sheet restored. (The mode
  // button also relabels to "Exit replay"; scope to the action menu's button.)
  await page.locator('#action-menu').getByRole('button', { name: 'Exit replay', exact: true }).click()
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
  const canvas = page.locator('canvas')
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
  const clickOnlyWire = async (): Promise<number> => {
    const s = await page.evaluate(() => {
      const v = window.__vpaDebug!.view()
      const ws = window.__vpaDebug!.wires()
      const w = ws[0]!
      return { x: w.x * v.scale + v.offsetX, y: w.y * v.scale + v.offsetY, n: ws.length }
    })
    await page.mouse.click(box.x + s.x, box.y + s.y)
    return s.n
  }
  // A guaranteed-empty click (far corner, off every node/wire and below the top
  // chrome) clears the current selection — the sheet region is never a hit.
  const clickEmpty = async (): Promise<void> => {
    await page.mouse.click(box.x + box.width - 2, box.y + box.height - 2)
  }

  // A closed lambda has only an output line, so the whole-node selection has a
  // single crossing wire → an arity-1 relation.
  await page.getByPlaceholder(/term, e\.g/).fill('\\x. x')
  await page.getByRole('button', { name: /add term/i }).click()
  await page.waitForTimeout(400) // let the layout settle so seam coords are current

  // Select the term node (click its body), then the EDIT menu offers Define.
  await clickTerm()
  await expect(page.locator('#status')).toContainText("node '")
  // Structural fingerprint of the sheet BEFORE defining: a conservative
  // definitional extension must leave it byte-identical (not just node-count).
  const sheetBefore = await page.evaluate(() => window.__vpaDebug!.editForm())
  expect(sheetBefore.length).toBeGreaterThan(0) // a real fingerprint, not a vacuous empty string
  await page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true }).click()
  await expect(page.locator('#status')).toContainText('click the crossing wires')

  // Pick the single crossing wire, name it, commit.
  expect(await clickOnlyWire()).toBe(1)
  await expect(page.locator('#status')).toContainText('1 argument wire(s) picked')
  await page.locator('#theorem-name').fill('R')
  await page.locator('#action-menu').getByRole('button', { name: /Commit relation definition/, exact: false }).click()
  await expect(page.locator('#status')).toContainText("defined 'R' (arity 1)")
  // The whole define flow (defineRelation + defineEntry) changed nothing on the
  // sheet — the canonical form is identical to the pre-define snapshot.
  expect(await page.evaluate(() => window.__vpaDebug!.editForm())).toBe(sheetBefore)

  // The Session group lists the new relation beside adopted theorems.
  const lib = page.locator('#library')
  await lib.getByRole('button', { name: /Session/, exact: false }).click()
  await expect(lib).toContainText('relations: R')

  // Folding is a CONSTRUCTION operation — no goals, no PROVE: select the node
  // right here in EDIT mode and fold it into the new relation.
  await clickEmpty()
  await clickTerm()
  await expect(page.locator('#status')).toContainText("node '")
  await page.getByPlaceholder(/term, e\.g/).fill('R') // fold reads the term input for the relation name
  await page.locator('#action-menu').getByRole('button', { name: /Fold into a relation/, exact: false }).click()
  expect(await clickOnlyWire()).toBe(1)
  await page.locator('#action-menu').getByRole('button', { name: /Commit fold into 'R'/, exact: false }).click()
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).some((b) => b.kind === 'ref'))
    .toBe(true)

  // Spawning: "Add relation" drops a fresh R reference with bare argument
  // wires — no need to rebuild the body and fold every time.
  const refsBefore = await page.evaluate(() => window.__vpaDebug!.bodies().filter((b) => b.kind === 'ref').length)
  await page.getByPlaceholder(/term, e\.g/).fill('R')
  await page.getByRole('button', { name: 'Add relation', exact: true }).click()
  await expect(page.locator('#status')).toContainText("added relation node")
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
    return { x: r.x * v.scale + v.offsetX, y: r.y * v.scale + v.offsetY }
  })
  await page.mouse.click(box.x + refPos.x, box.y + refPos.y)
  await expect(page.locator('#status')).toContainText("node '")
  await page.locator('#action-menu').getByRole('button', { name: 'Unfold relation', exact: true }).click()
  await expect(page.locator('#status')).toContainText('relation unfolded')
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).filter((b) => b.kind === 'term').length)
    .toBe(termsBefore + 1)

  // Save serializes the relation. Capture the live theory JSON (the same object
  // Save theory writes) and confirm it carries R.
  const json = await page.evaluate(() => window.__vpaDebug!.theoryJson())
  const theory = JSON.parse(json) as { relations: Record<string, unknown> }
  expect(theory.relations.R).toBeDefined()

  // Reload round-trip: a FRESH empty app loads the saved JSON through the real
  // #open-file-input; the loaded group lists R again.
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#open-file-input').setInputFiles({ name: 'saved.json', mimeType: 'application/json', buffer: Buffer.from(json) })
  const lib2 = page.locator('#library')
  await expect(lib2.getByRole('button', { name: 'Unload saved.json', exact: true })).toBeVisible()
  await lib2.getByRole('button', { name: '▸ saved.json', exact: true }).click()
  await expect(lib2).toContainText('relations: R')
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
  expect(Math.hypot(held.sx - target.sx, held.sy - target.sy)).toBeLessThan(30)
  await page.mouse.up()
  // after release the layout re-compacts (sibling attraction is a design
  // force), but the REARRANGEMENT persists: the dragged body settles on the
  // side it was dragged toward, relative to its sibling. Wait for actual
  // rest (bounded soft forces pace the return, so a fixed delay races).
  await page.waitForFunction(() => {
    const w = window as unknown as { __lastBodies?: string; __stable?: number }
    const now = JSON.stringify(window.__vpaDebug!.bodies().map((b) => [Math.round(b.x * 5), Math.round(b.y * 5)]))
    w.__stable = now === w.__lastBodies ? (w.__stable ?? 0) + 1 : 0
    w.__lastBodies = now
    return (w.__stable ?? 0) >= 3
  }, undefined, { polling: 250, timeout: 30000 })
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
