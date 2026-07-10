import { test, expect } from '@playwright/test'

async function spawnTerm(page: import('@playwright/test').Page, source: string): Promise<void> {
  const box = await page.locator('#c').boundingBox()
  if (box === null) throw new Error('the main canvas has no bounding box')
  const count = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  const x = box.x + box.width * (0.38 + (count % 3) * 0.12)
  const y = box.y + box.height * (0.42 + (Math.floor(count / 3) % 2) * 0.14)
  await page.mouse.click(x, y, { button: 'right' })
  const menu = page.getByRole('menu')
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

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      replay(): { mode: string; k: number; n: number; label: string; bodies: number }
      companion(): { visible: boolean; label: string; bodies: number; rebuilds: number; pos: { id: string; x: number; y: number }[] } | null
      view(): { scale: number; offsetX: number; offsetY: number }
      bodies(): { id: string; kind: string; x: number; y: number; r: number }[]
      wires(): { id: string; x: number; y: number }[]
      interaction(): { selected: readonly { kind: 'node' | 'region' | 'wire'; id: string }[]; pins: string[]; userZoom: number }
      theoryJson(): string
      editForm(): string
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

test('a goal proves end to end through the chrome', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  // build lhs: one identity node; snapshot as lhs (no citations, so this proves
  // against the empty boot context)
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  // set rhs = same diagram, prove with zero steps (met immediately)
  await page.getByRole('button', { name: /set goal rhs/i }).click()
  await page.getByRole('button', { name: /switch to prove/i }).click()
  await page.getByRole('button', { name: /assemble/i }).click()
  const status = await page.evaluate(() => window.__vpaDebug!.status())
  expect(status).toMatch(/assembled|checked|adopted/i)
})

// Plan 17: the PiP companion. Entering PROVE surfaces a view-only pane showing
// the OTHER side (the meet target). A forward step moves the main view but not
// the companion (its diagram identity — the backward side — is untouched). The
// toggle cycles PiP → split → hidden → PiP.
test('the companion pane targets the other side, survives a forward step, and toggles', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  const canvas = page.locator('#c')
  const box = (await canvas.boundingBox())!

  // A goal with a node on each side, so the backward-side companion has a body.
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  await page.getByRole('button', { name: /set goal rhs/i }).click()

  // EDIT: nothing to walk toward — the companion is not applicable.
  expect(await page.evaluate(() => window.__vpaDebug!.companion())).toBeNull()

  await page.getByRole('button', { name: /switch to prove/i }).click()

  // The pane appears (default PiP) showing the BACKWARD side, with a real body.
  await expect.poll(async () => (await page.evaluate(() => window.__vpaDebug!.companion()))?.bodies ?? 0).toBeGreaterThan(0)
  const c0 = await page.evaluate(() => window.__vpaDebug!.companion())
  expect(c0!.visible).toBe(true)
  expect(c0!.label).toBe('meeting: backward side')
  await expect(page.locator('#companion')).toBeVisible()

  // Apply a forward step: select the node, wrap it in a double cut. The forward
  // side gains a step (main view changes) while the companion tracks the
  // untouched backward side — same label, same body count, no reseed.
  await page.waitForTimeout(300)
  const s = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies().find((x) => x.kind === 'term')!
    return { x: b.x * v.scale + v.offsetX, y: b.y * v.scale + v.offsetY }
  })
  await page.mouse.click(box.x + s.x, box.y + s.y)
  await page.locator('#action-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true }).click()
  await expect(page.locator('#status')).toContainText('forward 1 step')
  const c1 = await page.evaluate(() => window.__vpaDebug!.companion())
  expect(c1!.label).toBe('meeting: backward side')
  expect(c1!.bodies).toBe(c0!.bodies)
  // Rebuild discipline: the forward step changed the MAIN diagram, not the
  // companion's target (the backward side), so the companion engine was NOT
  // reseeded — its reseed count is identical. (A per-frame rebuild would bump
  // this by dozens of frames between c0 and c1.)
  expect(c1!.rebuilds).toBe(c0!.rebuilds)

  // Toggle: PiP → split (right half) → hidden → PiP.
  const companionBtn = page.getByRole('button', { name: /^Companion:/ })
  await companionBtn.click()
  await expect(page.locator('#companion')).toBeVisible()
  // The next frame restyles pip (28vw) → split (50vw); poll for the resize.
  await expect.poll(async () => (await page.locator('#companion').boundingBox())!.width).toBeGreaterThan(box.width * 0.4)
  expect((await page.evaluate(() => window.__vpaDebug!.companion()))!.visible).toBe(true)

  // Split hit-testing: the MAIN camera fits the HALVED left half, so a node
  // renders in the left half — a real click at its rendered position must still
  // select it. (If the main camera ignored the halving, the node would render
  // centered UNDER the companion pane and the click would miss.) Re-read the
  // main box: it is now half-width.
  await page.waitForTimeout(200)
  const splitBox = (await canvas.boundingBox())!
  expect(splitBox.width).toBeLessThan(box.width * 0.75)
  const sn = await page.evaluate(() => {
    const v = window.__vpaDebug!.view()
    const b = window.__vpaDebug!.bodies().find((x) => x.kind === 'term')!
    return { id: b.id, x: b.x * v.scale + v.offsetX, y: b.y * v.scale + v.offsetY }
  })
  await page.mouse.click(splitBox.x + sn.x, splitBox.y + sn.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected)).toEqual([{ kind: 'node', id: sn.id }])

  await companionBtn.click()
  await expect(page.locator('#companion')).toBeHidden()
  // Still applicable (we are in PROVE), just not on-screen.
  const hidden = await page.evaluate(() => window.__vpaDebug!.companion())
  expect(hidden).not.toBeNull()
  expect(hidden!.visible).toBe(false)

  await companionBtn.click()
  await expect(page.locator('#companion')).toBeVisible()
})

// Plan 17 HARD RULE: the companion is VIEW-ONLY. A real click, drag, and wheel
// on the companion canvas must change NO state — no main-view zoom/pan, no
// selection, no pending action, and the companion itself must neither reseed nor
// change. (The companion canvas carries no pointer/wheel listeners; this pins
// that a gesture on it is completely inert, seam-diffed before/after.)
test('the companion canvas is inert: a click, drag, and wheel on it change nothing', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  // A goal with a node on each side, then enter PROVE — companion visible (PiP).
  await spawnTerm(page, '\\x. x')
  await page.getByRole('button', { name: /set goal lhs/i }).click()
  await page.getByRole('button', { name: /set goal rhs/i }).click()
  await page.getByRole('button', { name: /switch to prove/i }).click()
  await expect.poll(async () => (await page.evaluate(() => window.__vpaDebug!.companion()))?.bodies ?? 0).toBeGreaterThan(0)
  await expect(page.locator('#companion')).toBeVisible()
  await page.waitForTimeout(300) // let both engines settle so positions are at rest

  // Baseline: main camera, status, node count, and the companion's own state.
  const before = await page.evaluate(() => ({
    view: window.__vpaDebug!.view(),
    status: window.__vpaDebug!.status(),
    nodes: window.__vpaDebug!.nodeCount(),
    comp: window.__vpaDebug!.companion(),
  }))

  // Aim every gesture at the CENTER of the companion pane (bottom-right in PiP).
  const cbox = (await page.locator('#companion-canvas').boundingBox())!
  const cx = cbox.x + cbox.width / 2
  const cy = cbox.y + cbox.height / 2

  // A real click on the companion.
  await page.mouse.click(cx, cy)
  // A real drag across the companion.
  await page.mouse.move(cx, cy)
  await page.mouse.down()
  for (let i = 1; i <= 6; i++) await page.mouse.move(cx - i * 8, cy - i * 6)
  await page.mouse.up()
  // A real wheel over the companion (would zoom the MAIN view if it leaked).
  await page.mouse.move(cx, cy)
  await page.mouse.wheel(0, -400)
  await page.waitForTimeout(150)

  const after = await page.evaluate(() => ({
    view: window.__vpaDebug!.view(),
    status: window.__vpaDebug!.status(),
    nodes: window.__vpaDebug!.nodeCount(),
    comp: window.__vpaDebug!.companion(),
  }))

  // Main view unchanged: no wheel zoom (scale) and no drag pan (offsets).
  expect(Math.abs(after.view.scale - before.view.scale)).toBeLessThan(0.01)
  expect(Math.abs(after.view.offsetX - before.view.offsetX)).toBeLessThan(1)
  expect(Math.abs(after.view.offsetY - before.view.offsetY)).toBeLessThan(1)
  // No selection / pending action fired: the status message is byte-identical
  // (no "selected node '...'") and no node was created or removed.
  expect(after.status).toBe(before.status)
  expect(after.nodes).toBe(before.nodes)
  // The sheet has no selection — the action menu offers no node action.
  await expect(page.locator('#action-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true })).toHaveCount(0)
  // The companion itself neither reseeded nor changed its target, and its own
  // layout did not move (a drag on it does NOT drag its bodies — same ids, each
  // within rest micro-jitter of where it was).
  expect(after.comp!.rebuilds).toBe(before.comp!.rebuilds)
  expect(after.comp!.label).toBe(before.comp!.label)
  expect(after.comp!.bodies).toBe(before.comp!.bodies)
  expect(after.comp!.pos.map((p) => p.id).sort()).toEqual(before.comp!.pos.map((p) => p.id).sort())
  for (const b of before.comp!.pos) {
    const a = after.comp!.pos.find((p) => p.id === b.id)!
    expect(Math.hypot(a.x - b.x, a.y - b.y)).toBeLessThan(1)
  }
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
  await page.locator('#action-menu').getByRole('button', { name: 'Define relation…', exact: true }).click()
  await expect(page.locator('#status')).toContainText('argument order is canonical')

  // No wire picking needed: name it in the DEDICATED field and commit with the
  // canonical argument order. (Picking crossing wires remains an override.)
  await page.locator('#relation-name').fill('logic/R')
  await page.locator('#action-menu').getByRole('button', { name: /Commit relation definition \(canonical argument order\)/ }).click()
  await expect(page.locator('#status')).toContainText("defined 'logic/R' (arity 1)")
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
  await page.locator('#action-menu').getByRole('button', { name: 'Fold into a relation…', exact: true }).click()
  await page.locator('#action-menu').getByRole('button', { name: "Fold into 'logic/R'", exact: true }).click()
  await expect(page.locator('#status')).toContainText("folded into 'logic/R'")
  await expect
    .poll(async () => (await page.evaluate(() => window.__vpaDebug!.bodies())).some((b) => b.kind === 'ref'))
    .toBe(true)

  // The contextual cascade searches the live relation library and drops a
  // fresh qualified relation reference at the invocation point with bare argument wires.
  const refsBefore = await page.evaluate(() => window.__vpaDebug!.bodies().filter((b) => b.kind === 'ref').length)
  await spawnRelation(page, 'logic/R')
  await expect(page.locator('#status')).toContainText("relation 'logic/R' placed")
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
  await page.locator('#action-menu').getByRole('button', { name: 'Unfold relation', exact: true }).click()
  await expect(page.locator('#status')).toContainText('relation unfolded')
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
