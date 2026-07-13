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

test('ordinary proof abstraction is provisional, cancellable, marker-authored, and one-action finalizable', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnIdentity(page)
  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await page.waitForTimeout(350)
  const source = await page.evaluate(() => ({ status: window.__vpaDebug!.status(), nodes: window.__vpaDebug!.nodeCount() }))
  const term = await termClientPoint(page)
  await page.mouse.click(term.x, term.y)
  await page.keyboard.press('Shift+w')

  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(1)
  expect(await page.getByLabel('Bubble arity').count()).toBe(0)
  expect(await page.evaluate(() => window.__vpaDebug!.relationWorkspace())).toMatchObject({
    mode: 'abstract', transaction: { kind: 'empty-marker', markerSelected: true, canFinalize: true },
  })
  expect(await page.evaluate(() => ({ status: window.__vpaDebug!.status(), nodes: window.__vpaDebug!.nodeCount() }))).toEqual(source)

  await page.keyboard.press('Escape')
  await expect(page.locator('.vpa-relation-workspace')).toHaveCount(0)
  expect(await page.evaluate(() => ({ status: window.__vpaDebug!.status(), nodes: window.__vpaDebug!.nodeCount() }))).toEqual(source)
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
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(source.nodes + 1)
  await expect(page.locator('.vpa-refusal')).toHaveCount(0)
})

test('mounted normal abstraction derives matches, cycles sets, toggles exclusion, and opens backward', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
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
  await page.mouse.click(canvas.x + visibleTerm.x, canvas.y + visibleTerm.y)
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()!.transaction!.excludedKeys.length)).toBe(1)
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()

  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await openMode(page)
  await page.getByRole('button', { name: 'Prove backward', exact: true }).click()
  await page.waitForTimeout(250)
  const backwardTerm = await termClientPoint(page)
  await page.mouse.click(backwardTerm.x, backwardTerm.y)
  await page.keyboard.press('Shift+w')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.relationWorkspace()?.mode)).toBe('abstract')
  await page.getByRole('button', { name: 'Cancel', exact: true }).click()
})

test('both mounted fixed fronts open the same abstraction workspace and side switching cancels first', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await spawnIdentity(page)
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()

  for (const side of ['forward', 'backward'] as const) {
    const canvas = page.locator(`.vpa-proof-front-${side} canvas`)
    const box = (await canvas.boundingBox())!
    const point = await page.evaluate((selectedSide) => {
      const front = window.__vpaDebug!.fixed()![selectedSide]
      const body = front.bodies.find(({ kind }) => kind === 'term')!
      return { x: body.x * front.view.scale + front.view.offsetX, y: body.y * front.view.scale + front.view.offsetY }
    }, side)
    await page.mouse.click(box.x + point.x, box.y + point.y)
    await page.keyboard.press('Shift+w')
    await expect.poll(() => page.evaluate((selectedSide) => window.__vpaDebug!.fixed()![selectedSide].relationWorkspace?.mode, side)).toBe('abstract')
    if (side === 'forward') {
      const other = page.locator('.vpa-proof-front-backward canvas')
      const otherBox = (await other.boundingBox())!
      await page.mouse.click(otherBox.x + otherBox.width - 12, otherBox.y + 20)
      await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.forward.relationWorkspace)).toBeNull()
    } else {
      await page.getByRole('button', { name: 'Cancel', exact: true }).click()
      await expect.poll(() => page.evaluate(() => window.__vpaDebug!.fixed()!.backward.relationWorkspace)).toBeNull()
    }
  }
})
