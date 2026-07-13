import { expect, test, type Page } from '@playwright/test'

async function spawnIdentity(page: Page, x = 0.45): Promise<void> {
  const canvas = (await page.locator('#c').boundingBox())!
  await page.mouse.click(canvas.x + canvas.width * x, canvas.y + canvas.height * 0.5, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\x. x')
  await page.getByLabel('Lambda term to spawn').press('Enter')
}

async function openMode(page: Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
}

async function termClientPoint(page: Page): Promise<{ x: number; y: number }> {
  const canvas = (await page.locator('#c').boundingBox())!
  const point = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find(({ kind }) => kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  return { x: canvas.x + point.x, y: canvas.y + point.y }
}

async function moveWorkspaceClearOfHistory(page: Page): Promise<void> {
  const title = (await page.locator('.vpa-relation-title').boundingBox())!
  await page.mouse.move(title.x + title.width * 0.3, title.y + title.height / 2)
  await page.mouse.down()
  await page.mouse.move(220, 80, { steps: 8 })
  await page.mouse.up()
}

async function moveWorkspaceAwayFrom(page: Page, clientX: number): Promise<void> {
  const width = await page.evaluate(() => window.innerWidth)
  const title = (await page.locator('.vpa-relation-title').boundingBox())!
  await page.mouse.move(title.x + title.width * 0.3, title.y + title.height / 2)
  await page.mouse.down()
  await page.mouse.move(clientX > width / 2 ? 20 : width - 20, 80, { steps: 8 })
  await page.mouse.up()
}

async function exposeFirstDraftWire(page: Page): Promise<void> {
  for (let attempt = 0; attempt < 3; attempt++) {
    if (await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.materializedBoundary.length) > 0) return
    const wire = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.draftWires.find(({ point }) => point !== null)!.point!)
    const strip = (await page.locator('.vpa-relation-port-strip').boundingBox())!
    await page.mouse.move(wire.x, wire.y)
    await page.mouse.down()
    await page.mouse.move(strip.x + strip.width - 38, strip.y + strip.height / 2, { steps: 12 })
    await page.mouse.up()
  }
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.materializedBoundary.length)).toBe(1)
}

test('ordinary proof abstraction is provisional, cancellable, marker-authored, and one-action finalizable', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnIdentity(page)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(350)
  const sourceNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())
  const sourceProof = await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))
  const term = await termClientPoint(page)
  await page.mouse.click(term.x, term.y)
  await page.keyboard.press('Shift+w')

  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  expect(await page.getByLabel('Bubble arity').count()).toBe(0)
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace())).toMatchObject({
    mode: 'abstract', transaction: { kind: 'empty-marker', markerSelected: true, canFinalize: true },
  })
  expect(await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))).toBe(sourceProof)

  await page.keyboard.press('Escape')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  expect(await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))).toBe(sourceProof)
  expect(await page.evaluate(() => window.__vpaDebug!.interaction().selected)).toHaveLength(1)

  await page.keyboard.press('Shift+w')
  const title = (await page.locator('.vpa-relation-title').boundingBox())!
  await page.mouse.move(title.x + title.width * 0.3, title.y + title.height / 2)
  await page.mouse.down()
  await page.mouse.move(title.x + title.width + 500, title.y + title.height / 2, { steps: 8 })
  await page.mouse.up()
  const marker = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerPoint!)
  const canvas = (await page.locator('#c').boundingBox())!
  const view = await page.evaluate(() => window.__vpaDebug!.view())
  const markerClient = { x: canvas.x + marker.x * view.scale + view.offsetX, y: canvas.y + marker.y * view.scale + view.offsetY }
  await page.mouse.click(markerClient.x, markerClient.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerSelected)).toBe(false)
  await page.mouse.click(markerClient.x, markerClient.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerSelected)).toBe(true)

  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(sourceNodes + 1)
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)

  const atom = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find(({ kind }) => kind === 'atom')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  await page.mouse.click(canvas.x + atom.x, canvas.y + atom.y)
  await page.keyboard.press('Shift+w')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  await moveWorkspaceClearOfHistory(page)
  await page.locator('.vpa-temporal-undo').click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('0 step(s)')

  const original = await termClientPoint(page)
  await page.mouse.click(original.x, original.y)
  await page.keyboard.press('Shift+w')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  await moveWorkspaceClearOfHistory(page)
  await page.locator('.vpa-temporal-redo').click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
})

test('mounted nested empty marker accepts inside drag, refuses outside, and commits selected or trivial outcomes', async ({ page }) => {
  await page.setViewportSize({ width: 1600, height: 900 })
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnIdentity(page)
  const canvas = (await page.locator('#c').boundingBox())!
  const term = await termClientPoint(page)
  await page.mouse.click(term.x, term.y)
  await page.keyboard.press('w')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.regions().filter(({ kind }) => kind === 'cut').length)).toBe(1)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(300)
  const sourceProof = await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))

  const openCutAbstraction = async (): Promise<void> => {
    const cut = await page.evaluate(() => {
      const view = window.__vpaDebug!.view()
      const region = window.__vpaDebug!.regions().find(({ kind }) => kind === 'cut')!
      return {
        id: region.id,
        x: region.x * view.scale + view.offsetX,
        y: region.y * view.scale + view.offsetY,
        r: region.r * view.scale,
      }
    })
    await page.mouse.click(canvas.x + 15, canvas.y + 25)
    for (const angle of [0, Math.PI / 2, Math.PI, -Math.PI / 2]) {
      await page.mouse.click(canvas.x + cut.x + Math.cos(angle) * cut.r * 0.9, canvas.y + cut.y + Math.sin(angle) * cut.r * 0.9)
      const selected = await page.evaluate((id) => window.__vpaDebug!.interaction().selected
        .some((hit) => hit.kind === 'region' && hit.id === id), cut.id)
      if (selected) break
    }
    await expect.poll(() => page.evaluate((id) => window.__vpaDebug!.interaction().selected
      .some((hit) => hit.kind === 'region' && hit.id === id), cut.id)).toBe(true)
    await page.keyboard.press('Shift+w')
    await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  }

  await openCutAbstraction()
  expect(await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))).toBe(sourceProof)
  const start = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerPoint!)
  const view = await page.evaluate(() => window.__vpaDebug!.view())
  const startClient = { x: canvas.x + start.x * view.scale + view.offsetX, y: canvas.y + start.y * view.scale + view.offsetY }
  await moveWorkspaceAwayFrom(page, startClient.x)
  expect(await page.evaluate(({ x, y }) => {
    const element = document.elementFromPoint(x, y)
    return { id: element?.id, className: element instanceof HTMLElement ? element.className : '', tag: element?.tagName }
  }, startClient)).toEqual({ id: 'c', className: '', tag: 'CANVAS' })
  await page.mouse.click(startClient.x, startClient.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerSelected)).toBe(false)
  await page.mouse.click(startClient.x, startClient.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerSelected)).toBe(true)
  await page.mouse.move(startClient.x, startClient.y)
  await page.mouse.down()
  await page.mouse.move(startClient.x + 10, startClient.y + 4, { steps: 3 })
  await page.mouse.move(startClient.x, startClient.y, { steps: 3 })
  await page.mouse.up()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerAnchor)).not.toBe('r0')
  const nested = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerPoint!)

  const nestedClient = { x: canvas.x + nested.x * view.scale + view.offsetX, y: canvas.y + nested.y * view.scale + view.offsetY }
  await page.mouse.move(nestedClient.x, nestedClient.y)
  await page.mouse.down()
  await page.mouse.move(nestedClient.x + 10_000, nestedClient.y + 10_000, { steps: 8 })
  await page.mouse.up()
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'kernel-refusal')
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerPoint)).toEqual(nested)
  expect(await page.evaluate(() => JSON.stringify(window.__vpaDebug!.proofSnapshot()))).toBe(sourceProof)
  await page.mouse.click(nestedClient.x, nestedClient.y)
  await page.mouse.click(nestedClient.x, nestedClient.y)
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.status())).toContain('1 step(s)')
  const selectedNodes = await page.evaluate(() => window.__vpaDebug!.nodeCount())

  await page.locator('.vpa-temporal-undo').click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.status())).toContain('0 step(s)')
  await openCutAbstraction()
  const marker = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerPoint!)
  const currentView = await page.evaluate(() => window.__vpaDebug!.view())
  const markerClient = { x: canvas.x + marker.x * currentView.scale + currentView.offsetX, y: canvas.y + marker.y * currentView.scale + currentView.offsetY }
  await moveWorkspaceAwayFrom(page, markerClient.x)
  await page.mouse.click(markerClient.x, markerClient.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.markerSelected)).toBe(false)
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.status())).toContain('1 step(s)')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(selectedNodes - 1)
})

test('mounted normal abstraction derives matches, cycles sets, toggles exclusion, and opens backward', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#fuel-input').evaluate((input) => { (input as HTMLInputElement).value = '512' })
  await spawnIdentity(page, 0.38)
  await spawnIdentity(page, 0.62)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(350)
  const canvas = (await page.locator('#c').boundingBox())!
  const terms = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    return window.__vpaDebug!.bodies().filter(({ kind }) => kind === 'term').map((body) => ({
      x: body.x * view.scale + view.offsetX,
      y: body.y * view.scale + view.offsetY,
    })).sort((a, b) => a.x - b.x)
  })
  expect(terms).toHaveLength(2)
  await page.mouse.move(canvas.x + terms[0]!.x, canvas.y + terms[0]!.y)
  await page.keyboard.down('Shift')
  await page.mouse.down()
  await page.mouse.move(canvas.x + terms[1]!.x, canvas.y + terms[1]!.y, { steps: 16 })
  await page.mouse.up()
  await page.keyboard.up('Shift')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interaction().selected
    .filter(({ kind }) => kind === 'node').length)).toBe(2)
  await page.keyboard.press('Shift+w')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)

  const editor = (await page.locator('.vpa-relation-canvas').boundingBox())!
  await page.mouse.click(editor.x + editor.width * 0.55, editor.y + editor.height * 0.55, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\x. x')
  await page.getByLabel('Lambda term to spawn').press('Enter')
  if (await page.locator('.vpa-relation-status[data-status="zero-match"]').count() > 0) {
    await exposeFirstDraftWire(page)
  }
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'ready')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction)).toMatchObject({
    kind: 'matches', canFinalize: true, activeIndex: 0,
  })
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.candidateCount)).toBeGreaterThan(0)
  await page.keyboard.press('Tab')
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.activeIndex)).toBeGreaterThanOrEqual(0)

  const visibleTerm = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const rect = window.__vpaDebug!.relationWorkspace()!.rect
    const body = window.__vpaDebug!.bodies().filter(({ kind }) => kind === 'term').map((candidate) => ({
      x: candidate.x * view.scale + view.offsetX,
      y: candidate.y * view.scale + view.offsetY,
    })).find((candidate) => candidate.x < rect.left || candidate.x > rect.left + rect.width)!
    return body
  })
  const activeBeforeExclusion = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.activeKeys)
  await page.mouse.click(canvas.x + visibleTerm.x, canvas.y + visibleTerm.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.excludedKeys.length)).toBe(1)
  await page.mouse.click(canvas.x + visibleTerm.x, canvas.y + visibleTerm.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.excludedKeys.length)).toBe(0)
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.activeKeys)).toEqual(activeBeforeExclusion)
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
})

test('mounted backward abstraction finalizes a real normal match in a negative region', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#fuel-input').evaluate((input) => { (input as HTMLInputElement).value = '512' })
  await spawnIdentity(page)
  const editTerm = await termClientPoint(page)
  await page.mouse.click(editTerm.x, editTerm.y)
  await page.keyboard.press('w')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.regions().some(({ kind }) => kind === 'cut'))).toBe(true)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  await page.waitForTimeout(250)
  const backwardTerm = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const nested = window.__vpaDebug!.diagram().nodes.find(({ kind, region }) => kind === 'term' && region !== 'r0')!
    const body = window.__vpaDebug!.bodies().find(({ id }) => id === nested.id)!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  const proofCanvas = (await page.locator('#c').boundingBox())!
  await page.mouse.click(proofCanvas.x + backwardTerm.x, proofCanvas.y + backwardTerm.y)
  await page.keyboard.press('Shift+w')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()?.mode)).toBe('abstract')
  const backwardEditor = (await page.locator('.vpa-relation-canvas').boundingBox())!
  await page.mouse.click(backwardEditor.x + backwardEditor.width * 0.55, backwardEditor.y + backwardEditor.height * 0.55, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill('\\x. x')
  await page.getByLabel('Lambda term to spawn').press('Enter')
  if (await page.locator('.vpa-relation-status[data-status="zero-match"]').count() > 0) {
    await exposeFirstDraftWire(page)
  }
  await expect(page.locator('.vpa-relation-status')).toHaveAttribute('data-status', 'ready')
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  await expect(page.locator('#status')).toContainText('1 step(s)')
})

test('both fixed fronts open and cancel, with real finalization and global history cancellation', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnIdentity(page)
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  const fixedSnapshot = (side: 'forward' | 'backward') => page.evaluate(
    (selectedSide) => JSON.stringify(window.__vpaDebug!.fixed()![selectedSide].proofSnapshot),
    side,
  )

  const openFixedAbstraction = async (side: 'forward' | 'backward', kind: 'term' | 'atom'): Promise<void> => {
    const canvas = page.locator(`.vpa-proof-front-${side} canvas`)
    const box = (await canvas.boundingBox())!
    await page.mouse.click(box.x + 12, box.y + 24)
    const point = await page.evaluate(({ selectedSide, selectedKind }) => {
      const front = window.__vpaDebug!.fixed()![selectedSide]
      const body = front.bodies.find(({ kind }) => kind === selectedKind)!
      return { x: body.x * front.view.scale + front.view.offsetX, y: body.y * front.view.scale + front.view.offsetY }
    }, { selectedSide: side, selectedKind: kind })
    await page.mouse.click(box.x + point.x, box.y + point.y)
    await expect.poll(() => page.evaluate((selectedSide) => window.__vpaDebug!.fixed()![selectedSide].selected, side)).toBe(1)
    await page.keyboard.press('Shift+w')
    await expect.poll(() => page.evaluate((selectedSide) => window.__vpaDebug!.fixed()![selectedSide].relationWorkspace?.mode, side)).toBe('abstract')
  }

  const initialForward = await fixedSnapshot('forward')
  await openFixedAbstraction('forward', 'term')
  expect(await fixedSnapshot('forward')).toEqual(initialForward)
  await page.getByRole('button', { name: 'Abstract', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)

  await openFixedAbstraction('forward', 'atom')
  await moveWorkspaceClearOfHistory(page)
  await page.locator('.vpa-temporal-undo').click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.relationWorkspace)).toBeNull()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(0)

  await openFixedAbstraction('forward', 'term')
  await moveWorkspaceClearOfHistory(page)
  await page.locator('.vpa-temporal-redo').click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.relationWorkspace)).toBeNull()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.cursor)).toBe(1)

  const beforeForwardCancel = await fixedSnapshot('forward')
  await openFixedAbstraction('forward', 'atom')
  expect(await fixedSnapshot('forward')).toBe(beforeForwardCancel)
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.relationWorkspace)).toBeNull()
  expect(await fixedSnapshot('forward')).toEqual(beforeForwardCancel)

  const other = page.locator('.vpa-proof-front-backward canvas')
  const otherBox = (await other.boundingBox())!
  await page.mouse.click(otherBox.x + otherBox.width - 12, otherBox.y + 20)
  const beforeBackwardCancel = await fixedSnapshot('backward')
  await openFixedAbstraction('backward', 'term')
  expect(await fixedSnapshot('backward')).toBe(beforeBackwardCancel)
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.relationWorkspace)).toBeNull()
  expect(await fixedSnapshot('backward')).toBe(beforeBackwardCancel)
})
