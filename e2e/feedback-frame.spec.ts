import { expect, test, type Page } from '@playwright/test'

type Variant = 'a' | 'b' | 'c'

async function openVariant(page: Page, variant: Variant): Promise<void> {
  await page.goto(`http://127.0.0.1:4174/ui-lab/round17-${variant}.html`)
  await expect(page.locator('#layout-root')).toHaveAttribute('data-ready', 'true')
  await expect(page.locator('#layout-root')).toHaveAttribute('data-feedback-prototype', variant === 'a' ? 'field' : variant === 'b' ? 'ribbon' : 'chronicle')
  await expect(page.locator('.layout-feedback')).toBeHidden()
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

async function currentFeedback(page: Page) {
  return page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __vpaDebug?: { feedback(): unknown } } | null)?.__vpaDebug?.feedback(),
  )
}

test('all projections consume the same typed authority without the legacy bottom toast', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    expect(await currentFeedback(page)).toMatchObject({
      current: {
        sequence: 1,
        kind: 'ambient',
        owner: { kind: 'control', id: 'mode' },
        persistence: 'state',
      },
      problems: [],
    })
    await expect(page.locator('.layout-feedback')).toBeHidden()
  }
})

test('the real pin gesture reports owned guidance and a real committed result in every projection', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    const body = await bodyPoint(page)
    await page.mouse.move(body.x, body.y)
    await page.keyboard.down('Control')
    await page.mouse.down()
    await page.mouse.move(body.x + 45, body.y + 24, { steps: 10 })
    await expect.poll(() => currentFeedback(page)).toMatchObject({
      current: { kind: 'guidance', owner: { kind: 'node', id: body.id }, persistence: 'interaction' },
    })
    await page.keyboard.up('Control')
    await expect.poll(() => currentFeedback(page)).toMatchObject({
      current: { kind: 'guidance', text: 'release the pointer to pin this node' },
    })
    await page.mouse.up()
    await expect.poll(() => currentFeedback(page)).toMatchObject({
      current: { kind: 'success', owner: { kind: 'node', id: body.id }, affected: [{ kind: 'node', id: body.id }] },
    })
    await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
      (frame.contentWindow as Window & { __vpaDebug?: { interaction(): { pins: string[] } } } | null)?.__vpaDebug?.interaction().pins,
    )).toContain(body.id)

    if (variant === 'a') {
      // The committed pin marker is already visible authoritative state: Field
      // Signals deliberately adds no duplicate prose or success halo.
      await expect(page.locator('.feedback-pulse')).toBeHidden()
      await expect(page.locator('.feedback-callout')).toBeHidden()
    } else if (variant === 'b') {
      await expect(page.locator('.feedback-callout')).toContainText('pinned node')
    } else {
      await expect(page.locator('.feedback-chronicle-row')).toContainText('pinned node')
    }
  }
})

test('invalid real field state persists as one problem and clears when corrected', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    const body = await bodyPoint(page)
    await page.mouse.click(body.x, body.y)
    await page.keyboard.press('Shift+W')
    const input = page.frameLocator('.layout-app').locator('.vpa-bubble-arity')
    await expect(input).toBeVisible()
    await input.fill('-1')
    await input.press('Enter')
    await expect.poll(() => currentFeedback(page)).toMatchObject({
      current: {
        kind: 'problem',
        owner: { kind: 'control', id: 'bubble-arity' },
        persistence: 'problem',
        problemId: 'bubble-arity',
      },
      problems: [{ problemId: 'bubble-arity' }],
    })
    if (variant === 'c') await expect(page.locator('.feedback-chronicle-row.is-problem')).toBeVisible()
    else await expect(page.locator('.feedback-issue-button')).toContainText('1 unresolved issue')

    await input.fill('2')
    await expect.poll(() => currentFeedback(page)).toMatchObject({ current: null, problems: [] })
  }
})

test('a real parser refusal stays verbatim and local in every projection', async ({ page }) => {
  for (const variant of ['a', 'b', 'c'] as const) {
    await openVariant(page, variant)
    const frame = await page.locator('.layout-app').boundingBox()
    if (frame === null) throw new Error('the actual app frame has no box')
    await page.mouse.click(frame.x + frame.width * 0.76, frame.y + frame.height * 0.72, { button: 'right' })
    const app = page.frameLocator('.layout-app')
    await app.locator('.vpa-spawn-row').filter({ hasText: 'λ term' }).click()
    const term = app.getByLabel('Lambda term to spawn')
    await term.fill('\\x.')
    await term.press('Enter')
    const state = await currentFeedback(page) as { current: { kind: string; text: string; owner: { kind: string } }; problems: unknown[] }
    expect(state.current).toMatchObject({ kind: 'refusal', owner: { kind: 'point' } })
    expect(state.current.text.length).toBeGreaterThan(0)
    expect(state.problems).toEqual([])
    await expect(page.locator('.feedback-callout')).toHaveText(state.current.text)
  }
})

test('replay feedback points to the real history control while source errors remain in Sources', async ({ page }) => {
  await openVariant(page, 'a')
  await page.locator('.layout-library-button').click()
  await page.locator('.lib-mode-tabs button').filter({ hasText: 'Sources' }).click()
  await expect(page.locator('.lib-source-row[data-source-file="broken.json"] .lib-source-error')).toBeVisible()
  expect(await currentFeedback(page)).toMatchObject({ problems: [] })

  await page.locator('.lib-mode-tabs button').filter({ hasText: 'Browse' }).click()
  await page.locator('.lib-item-row[data-item-name="plusAssoc"]').click()
  await page.locator('.lib-replay').click()
  const range = page.locator('.layout-time-range')
  await expect(range).toBeEnabled()
  await range.fill('3')
  await expect.poll(() => currentFeedback(page)).toMatchObject({
    current: { kind: 'history', owner: { kind: 'control', id: 'history' }, persistence: 'state' },
    problems: [],
  })
  await expect.poll(() => page.locator('.layout-app').evaluate((frame: HTMLIFrameElement) =>
    (frame.contentWindow as Window & { __vpaDebug?: { replay(): { k: number } } } | null)?.__vpaDebug?.replay().k,
  )).toBe(3)
})
