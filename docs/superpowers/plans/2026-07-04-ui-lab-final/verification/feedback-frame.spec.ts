import { expect, test, type Page } from '@playwright/test'

type FeedbackState = {
  refusal: { sequence: number; text: string; pointer: { x: number; y: number }; expiresAt: number } | null
  problems: { id: string; text: string }[]
}

async function openApproved(page: Page): Promise<void> {
  await page.goto('http://127.0.0.1:4174/ui-lab/round17-a.html')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-ready', 'true')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-feedback-model', 'error-only')
}

async function bodyPoint(page: Page): Promise<{ id: string; x: number; y: number }> {
  const local = await page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) => {
    const debug = (frame.contentWindow as Window & {
      __vpaDebug?: {
        bodies(): { id: string; kind: string; x: number; y: number }[]
        view(): { scale: number; offsetX: number; offsetY: number }
      }
    } | null)?.__vpaDebug
    if (debug === undefined) throw new Error('the actual app debug seam is missing')
    const body = debug.bodies().find((candidate) => candidate.kind === 'ref')
    if (body === undefined) throw new Error('the verified fixture has no relation node')
    const view = debug.view()
    return { id: body.id, x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  const frame = await page.locator('.layout-app').boundingBox()
  if (frame === null) throw new Error('the actual app frame has no box')
  return { id: local.id, x: frame.x + local.x, y: frame.y + local.y }
}

async function currentFeedback(page: Page): Promise<FeedbackState> {
  return page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) => {
    const state = (frame.contentWindow as Window & { __vpaDebug?: { feedback(): unknown } } | null)?.__vpaDebug?.feedback()
    if (state === undefined) throw new Error('feedback debug seam is absent')
    return state as FeedbackState
  })
}

test('only the approved error-only presentation exists', async ({ page }) => {
  await openApproved(page)
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })
  await expect(page.locator('.feedback-pulse,.feedback-chronicle,.feedback-issues,.layout-feedback')).toHaveCount(0)
  await expect(page.locator('a[href*="round17-b"],a[href*="round17-c"]')).toHaveCount(0)
})

test('selection is silent and actions appear only after explicit right-click at that point', async ({ page }) => {
  await openApproved(page)
  const body = await bodyPoint(page)
  const app = page.frameLocator('.layout-app')

  await page.mouse.click(body.x, body.y)
  await expect(app.locator('#action-menu')).toBeHidden()
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })

  await page.mouse.click(body.x, body.y, { button: 'right' })
  await expect(app.locator('#action-menu')).toBeVisible()
  const palette = await app.locator('#action-menu').boundingBox()
  if (palette === null) throw new Error('the action palette has no box')
  expect(Math.abs(palette.x - body.x)).toBeLessThan(40)
  expect(Math.abs(palette.y - body.y)).toBeLessThan(40)
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })
})

test('pinning changes authoritative pin state without producing a message', async ({ page }) => {
  await openApproved(page)
  const body = await bodyPoint(page)
  await page.mouse.move(body.x, body.y)
  await page.keyboard.down('Control')
  await page.mouse.down()
  await page.mouse.move(body.x + 45, body.y + 24, { steps: 10 })
  await page.keyboard.up('Control')
  await page.mouse.up()

  await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __vpaDebug?: { interaction(): { pins: string[] } } } | null)?.__vpaDebug?.interaction().pins,
  )).toContain(body.id)
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })
  await expect(page.frameLocator('.layout-app').locator('.vpa-refusal')).toHaveCount(0)
})

test('invalid arity is owned inline by its field and clears immediately when corrected', async ({ page }) => {
  await openApproved(page)
  const body = await bodyPoint(page)
  await page.mouse.click(body.x, body.y)
  await page.keyboard.press('Shift+W')
  const app = page.frameLocator('.layout-app')
  const input = app.locator('.vpa-bubble-arity')
  const problem = app.locator('#bubble-arity-problem')
  await input.fill('-1')
  await input.press('Enter')

  await expect(input).toHaveAttribute('aria-invalid', 'true')
  await expect(input).toHaveAttribute('aria-describedby', 'bubble-arity-problem')
  await expect(problem).toHaveText("'-1' is not a valid arity")
  await expect(problem).toBeVisible()
  expect(await currentFeedback(page)).toEqual({
    refusal: null,
    problems: [{ id: 'bubble-arity', text: "'-1' is not a valid arity" }],
  })

  await input.fill('2')
  await expect(problem).toBeHidden()
  await expect(input).not.toHaveAttribute('aria-invalid', 'true')
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })
})

test('a parser refusal stays verbatim beside the current pointer and does not enter history', async ({ page }) => {
  await openApproved(page)
  const frame = await page.locator('.layout-app').boundingBox()
  if (frame === null) throw new Error('the actual app frame has no box')
  const pointer = { x: frame.x + frame.width * 0.76, y: frame.y + frame.height * 0.72 }
  await page.mouse.click(pointer.x, pointer.y, { button: 'right' })
  const app = page.frameLocator('.layout-app')
  await app.locator('.vpa-spawn-row').filter({ hasText: 'λ term' }).click()
  const term = app.getByLabel('Lambda term to spawn')
  await term.fill('\\x.')
  await term.press('Enter')

  const state = await currentFeedback(page)
  expect(state.refusal?.text.length).toBeGreaterThan(0)
  expect(state.problems).toEqual([])
  const refusal = app.locator('.vpa-refusal')
  await expect(refusal).toHaveText(state.refusal!.text)
  await expect(refusal).toHaveAttribute('role', 'alert')
  const box = await refusal.boundingBox()
  if (box === null) throw new Error('the refusal has no box')
  const horizontalEdgeDistance = Math.min(Math.abs(box.x - pointer.x), Math.abs(box.x + box.width - pointer.x))
  const verticalEdgeDistance = Math.min(Math.abs(box.y - pointer.y), Math.abs(box.y + box.height - pointer.y))
  expect(Math.min(horizontalEdgeDistance, verticalEdgeDistance)).toBeLessThan(40)
  expect(pointer.x < box.x || pointer.x > box.x + box.width || pointer.y < box.y || pointer.y > box.y + box.height).toBe(true)
})

test('history scrubbing and source errors remain with their own controls', async ({ page }) => {
  await openApproved(page)
  await page.locator('.layout-library-button').click()
  await page.locator('.lib-mode-tabs button').filter({ hasText: 'Sources' }).click()
  await expect(page.locator('.lib-source-row[data-source-file="broken.json"] .lib-source-error')).toBeVisible()
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })

  await page.locator('.lib-mode-tabs button').filter({ hasText: 'Browse' }).click()
  await page.locator('.lib-item-row[data-item-name="plusAssoc"]').click()
  await page.locator('.lib-replay').click()
  const range = page.locator('.layout-time-range')
  await expect(range).toBeEnabled()
  await range.fill('3')
  await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __vpaDebug?: { replay(): { k: number } } } | null)?.__vpaDebug?.replay().k,
  )).toBe(3)
  expect(await currentFeedback(page)).toEqual({ refusal: null, problems: [] })
})
