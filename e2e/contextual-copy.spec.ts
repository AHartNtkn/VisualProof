import { expect, test, type Page } from '@playwright/test'

async function spawnTerm(page: Page, source: string, x: number): Promise<void> {
  const canvas = (await page.locator('#c').boundingBox())!
  await page.mouse.click(canvas.x + canvas.width * x, canvas.y + canvas.height * 0.5, { button: 'right' })
  await page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true }).click()
  await page.getByLabel('Lambda term to spawn').fill(source)
  await page.getByLabel('Lambda term to spawn').press('Enter')
}

async function openMode(page: Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
}

async function pageBody(page: Page, index = 0): Promise<{ x: number; y: number }> {
  const canvas = (await page.locator('#c').boundingBox())!
  const point = await page.evaluate((selectedIndex) => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().filter(({ kind }) => kind === 'term')[selectedIndex]!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  }, index)
  return { x: canvas.x + point.x, y: canvas.y + point.y }
}

async function moveWorkspaceAwayFrom(page: Page, x: number): Promise<void> {
  const title = (await page.locator('.vpa-relation-title').boundingBox())!
  const width = await page.evaluate(() => innerWidth)
  await page.mouse.move(title.x + title.width * 0.3, title.y + title.height / 2)
  await page.mouse.down()
  await page.mouse.move(x < width / 2 ? width - 30 : 30, 75, { steps: 10 })
  await page.mouse.up()
}

test('selected host content copies into the shared workspace as one loose, port-free draft action', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, 'y', 0.45)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()

  const source = await pageBody(page)
  await page.mouse.click(source.x, source.y)
  await page.keyboard.press('Shift+w')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  await moveWorkspaceAwayFrom(page, source.x)
  const liveSource = await pageBody(page)
  expect(await page.evaluate(({ x, y }) => document.elementFromPoint(x, y)?.id, liveSource)).toBe('c')
  const before = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!)
  expect(before.draftBodies.filter(({ kind }) => kind === 'term')).toHaveLength(0)
  expect(before.materializedBoundary).toEqual([])

  const workspace = (await page.locator('.vpa-relation-canvas').boundingBox())!
  const drop = { x: workspace.x + workspace.width * 0.7, y: workspace.y + workspace.height * 0.62 }
  await page.mouse.move(liveSource.x, liveSource.y)
  await page.mouse.down()
  await page.mouse.move(drop.x, drop.y, { steps: 16 })
  await page.mouse.up()

  const after = await page.evaluate(() => window.__vpaDebug!.relationWorkspace()!)
  expect(after.cursor).toBe(before.cursor + 1)
  expect(after.historyLength).toBe(before.historyLength + 1)
  const copiedTerms = after.draftBodies.filter(({ kind }) => kind === 'term')
  expect(copiedTerms).toHaveLength(1)
  expect(after.draftWires).toHaveLength(2)
  expect(after.draftWires.every(({ wire }) => wire.startsWith('copy_boundary_'))).toBe(true)
  expect(after.materializedBoundary).toEqual([])
  await expect(page.locator('.vpa-relation-port')).toHaveCount(0)
  expect(Math.hypot(copiedTerms[0]!.point.x - drop.x, copiedTerms[0]!.point.y - drop.y)).toBeLessThan(55)
})

test('Ctrl keeps copy unclaimed while a construction fallback commits one grouped action and one undo stop', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x', 0.5)
  const canvas = (await page.locator('#c').boundingBox())!
  const selectRegion = async (id: string): Promise<{ x: number; y: number }> => {
    const region = await page.evaluate((regionId) => {
      const view = window.__vpaDebug!.view()
      const found = window.__vpaDebug!.regions().find(({ id }) => id === regionId)!
      return {
        x: found.x * view.scale + view.offsetX,
        y: found.y * view.scale + view.offsetY,
        r: found.r * view.scale,
      }
    }, id)
    for (const angle of [0, Math.PI / 2, Math.PI, -Math.PI / 2]) {
      const point = { x: canvas.x + region.x + Math.cos(angle) * region.r * 0.9, y: canvas.y + region.y + Math.sin(angle) * region.r * 0.9 }
      await page.mouse.click(point.x, point.y)
      if (await page.evaluate((regionId) => window.__vpaDebug!.interaction().selected.some((hit) => hit.kind === 'region' && hit.id === regionId), id)) return point
    }
    throw new Error(`could not select region ${id}`)
  }
  const term = await pageBody(page)
  await page.mouse.click(term.x, term.y)
  await page.keyboard.press('w')
  for (let depth = 1; depth < 3; depth++) {
    await expect.poll(() => page.evaluate(() => window.__vpaDebug!.regions().filter(({ kind }) => kind === 'cut').length)).toBe(depth)
    const outer = await page.evaluate(() => window.__vpaDebug!.regions().find(({ kind, parent }) => kind === 'cut' && parent === 'r0')!.id)
    await page.mouse.click(canvas.x + 18, canvas.y + canvas.height - 18)
    await selectRegion(outer)
    await page.keyboard.press('w')
  }
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.regions().filter(({ kind }) => kind === 'cut').length)).toBe(3)

  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(300)
  const hierarchy = await page.evaluate(() => {
    const cuts = window.__vpaDebug!.regions().filter(({ kind }) => kind === 'cut')
    const outer = cuts.find(({ parent }) => parent === 'r0')!
    const middle = cuts.find(({ parent }) => parent === outer.id)!
    return { outer: outer.id, middle: middle.id }
  })
  await page.mouse.click(canvas.x + 18, canvas.y + canvas.height - 18)
  let regionStart = await selectRegion(hierarchy.middle)
  await expect.poll(() => page.evaluate((id) => window.__vpaDebug!.interaction().selected).then((selection) => selection)).toEqual([{ kind: 'region', id: hierarchy.middle }])

  const nestedTerm = await pageBody(page)
  const destination = { x: canvas.x + 55, y: canvas.y + canvas.height - 70 }
  const beforePhysics = await page.evaluate(() => window.__vpaDebug!.proofSnapshot()!)
  const physicalBody = await page.evaluate(() => {
    const body = window.__vpaDebug!.bodies().find(({ kind }) => kind === 'term')!
    return { id: body.id, x: body.x, y: body.y }
  })
  await page.keyboard.down('Control')
  await page.mouse.move(nestedTerm.x, nestedTerm.y)
  await page.mouse.down()
  const physicsTarget = { x: nestedTerm.x + 10, y: nestedTerm.y + 45 }
  await page.mouse.move(physicsTarget.x, physicsTarget.y, { steps: 16 })
  await page.waitForTimeout(120)
  expect(await page.evaluate(() => window.__vpaDebug!.interactionOverlays())).not.toEqual(['circle', 'circle'])
  const duringPhysics = await page.evaluate(({ id, canvasX, canvasY }) => {
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.id === id)!
    const view = window.__vpaDebug!.view()
    return { x: canvasX + body.x * view.scale + view.offsetX, y: canvasY + body.y * view.scale + view.offsetY }
  }, { id: physicalBody.id, canvasX: canvas.x, canvasY: canvas.y })
  expect(Math.hypot(duringPhysics.x - physicsTarget.x, duringPhysics.y - physicsTarget.y)).toBeLessThan(25)
  await page.mouse.up()
  await page.keyboard.up('Control')
  expect(await page.evaluate(() => window.__vpaDebug!.proofSnapshot()!.actions.length)).toBe(beforePhysics.actions.length)

  await page.mouse.click(canvas.x + 18, canvas.y + canvas.height - 18)
  regionStart = await selectRegion(hierarchy.middle)
  await page.mouse.move(regionStart.x, regionStart.y)
  await page.mouse.down()
  await page.mouse.move(destination.x, destination.y, { steps: 12 })
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interactionOverlays())).toEqual(['circle', 'circle'])
  await page.mouse.up()

  const committed = await page.evaluate(() => window.__vpaDebug!.proofSnapshot()!)
  expect(committed.cursor).toBe(1)
  expect(committed.actions).toHaveLength(1)
  expect(committed.actions[0]!.steps).toHaveLength(2)
  expect(committed.actions[0]!.steps.map((step: any) => step.rule)).toEqual(['doubleCutIntro', 'closedTermIntro'])
  await expect(page.locator('#status')).toContainText('1 action')
  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.proofSnapshot()!.cursor)).toBe(0)
  await page.keyboard.press('Control+Shift+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.proofSnapshot()!.cursor)).toBe(1)

  await page.getByPlaceholder('theorem name').fill('copyFallback')
  await page.getByRole('button', { name: 'Declare / assemble + check', exact: true }).click()
  const saved = await page.evaluate(() => window.__vpaDebug!.theoryJson())
  const theorem = (JSON.parse(saved) as any).theorems.find((candidate: any) => candidate.name === 'copyFallback')
  expect(theorem.actions).toHaveLength(1)
  expect(theorem.actions[0].steps).toHaveLength(2)

  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#open-file-input').setInputFiles({
    name: 'saved-copy.json', mimeType: 'application/json', buffer: Buffer.from(saved),
  })
  const library = page.locator('#library')
  await library.getByRole('button', { name: '▸ saved-copy.json', exact: true }).click()
  await expect(library).toContainText('copyFallback (1 action)')
  await library.getByRole('button', { name: '▶ Replay', exact: true }).click()
  expect(await page.evaluate(() => window.__vpaDebug!.replay().n)).toBe(1)
  await page.keyboard.press('ArrowRight')
  expect(await page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(1)
})

test('genuine iteration uses the same mounted green copy preview and one action stop', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x', 0.38)
  await spawnTerm(page, '\\y. y', 0.62)
  const wrapped = await pageBody(page, 1)
  await page.mouse.click(wrapped.x, wrapped.y)
  await page.keyboard.press('w')
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(250)

  const canvas = (await page.locator('#c').boundingBox())!
  const geometry = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const source = window.__vpaDebug!.bodies().find(({ kind, region }) => kind === 'term' && region === 'r0')!
    const target = window.__vpaDebug!.regions().find(({ kind }) => kind === 'cut')!
    return {
      source: { x: source.x * view.scale + view.offsetX, y: source.y * view.scale + view.offsetY },
      target: { x: target.x * view.scale + view.offsetX, y: target.y * view.scale + view.offsetY },
    }
  })
  const source = { x: canvas.x + geometry.source.x, y: canvas.y + geometry.source.y }
  const target = { x: canvas.x + geometry.target.x, y: canvas.y + geometry.target.y }
  await page.mouse.click(source.x, source.y)
  await page.mouse.move(source.x, source.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y, { steps: 12 })
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interactionOverlays())).toEqual(['circle', 'circle'])
  await page.mouse.up()

  const proof = await page.evaluate(() => window.__vpaDebug!.proofSnapshot()!)
  expect(proof.cursor).toBe(1)
  expect(proof.actions).toHaveLength(1)
  expect(proof.actions[0]!.steps).toMatchObject([{ rule: 'iteration' }])
  await expect(page.locator('#status')).toContainText('1 action')
})

test('ordinary backward proving exposes the same contextual copy gesture and atomic undo', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x', 0.38)
  await spawnTerm(page, '\\y. y', 0.62)
  const wrapped = await pageBody(page, 1)
  await page.mouse.click(wrapped.x, wrapped.y)
  await page.keyboard.press('w')
  await openMode(page)
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  await page.waitForTimeout(250)

  const canvas = (await page.locator('#c').boundingBox())!
  const geometry = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const source = window.__vpaDebug!.bodies().find(({ kind, region }) => kind === 'term' && region === 'r0')!
    const target = window.__vpaDebug!.regions().find(({ kind }) => kind === 'cut')!
    return {
      source: { x: source.x * view.scale + view.offsetX, y: source.y * view.scale + view.offsetY },
      target: { x: target.x * view.scale + view.offsetX, y: target.y * view.scale + view.offsetY },
    }
  })
  const source = { x: canvas.x + geometry.source.x, y: canvas.y + geometry.source.y }
  const target = { x: canvas.x + geometry.target.x, y: canvas.y + geometry.target.y }
  await page.mouse.click(source.x, source.y)
  await page.mouse.move(source.x, source.y)
  await page.mouse.down()
  await page.mouse.move(target.x, target.y, { steps: 12 })
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.interactionOverlays())).toEqual(['circle', 'circle'])
  await page.mouse.up()

  const proof = await page.evaluate(() => window.__vpaDebug!.proofSnapshot()!)
  expect(proof.cursor).toBe(1)
  expect(proof.actions).toHaveLength(1)
  expect(proof.actions[0]!.steps).toMatchObject([{ rule: 'iteration' }])
  await page.keyboard.press('Control+z')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.proofSnapshot()!.cursor)).toBe(0)
})

test('both fixed fronts expose the same contextual copy preview, atomic action, and isolated undo', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnTerm(page, '\\x. x', 0.38)
  await spawnTerm(page, '\\y. y', 0.62)
  const wrapped = await pageBody(page, 1)
  await page.mouse.click(wrapped.x, wrapped.y)
  await page.keyboard.press('w')
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  for (const side of ['forward', 'backward'] as const) {
    const other = side === 'forward' ? 'backward' : 'forward'
    const canvas = page.locator(`.vpa-proof-front-${side} .vpa-proof-front-canvas`)
    const box = (await canvas.boundingBox())!
    const geometry = await page.evaluate((selectedSide) => {
      const front = window.__vpaDebug!.fixed()![selectedSide]
      const target = front.regions.find(({ kind }) => kind === 'cut')!
      const source = front.bodies.find(({ kind, x, y }) => kind === 'term'
        && Math.hypot(x - target.x, y - target.y) > target.r)!
      return {
        source: { x: source.x * front.view.scale + front.view.offsetX, y: source.y * front.view.scale + front.view.offsetY },
        target: { x: target.x * front.view.scale + front.view.offsetX, y: target.y * front.view.scale + front.view.offsetY },
      }
    }, side)
    const source = { x: box.x + geometry.source.x, y: box.y + geometry.source.y }
    const target = { x: box.x + geometry.target.x, y: box.y + geometry.target.y }
    await page.mouse.click(source.x, source.y)
    await page.mouse.move(source.x, source.y)
    await page.mouse.down()
    await page.mouse.move(target.x, target.y, { steps: 12 })
    await expect.poll(() => page.evaluate((selectedSide) => window.__vpaDebug!.fixed()![selectedSide].interactionOverlays, side)).toEqual(['circle', 'circle'])
    await page.mouse.up()

    const fixed = await page.evaluate(() => window.__vpaDebug!.fixed()!)
    expect(fixed[side].cursor).toBe(1)
    expect(fixed[side].proofSnapshot.actions).toHaveLength(1)
    expect(fixed[side].proofSnapshot.actions[0]!.steps).toMatchObject([{ rule: 'iteration' }])
    expect(fixed[other].cursor).toBe(0)
    await page.keyboard.press('Control+z')
    await expect.poll(() => page.evaluate((selectedSide) => window.__vpaDebug!.fixed()![selectedSide].cursor, side)).toBe(0)
    expect(await page.evaluate((otherSide) => window.__vpaDebug!.fixed()![otherSide].cursor, other)).toBe(0)
  }
})
