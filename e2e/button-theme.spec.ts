import { expect, test, type Locator, type Page } from '@playwright/test'

type RenderedControl = { color: string; background: string; border: string; contrast: number }

async function rendered(locator: Locator): Promise<RenderedControl> {
  return locator.evaluate((element) => {
    const parse = (css: string): [number, number, number, number] => {
      const values = css.match(/[\d.]+/g)?.map(Number) ?? []
      return [values[0] ?? 0, values[1] ?? 0, values[2] ?? 0, values[3] ?? 1]
    }
    const over = (front: number[], back: number[]): [number, number, number, number] => {
      const alpha = front[3]! + back[3]! * (1 - front[3]!)
      if (alpha === 0) return [0, 0, 0, 0]
      const channels = [0, 1, 2].map((index) => (
        front[index]! * front[3]! + back[index]! * back[3]! * (1 - front[3]!)
      ) / alpha)
      return [channels[0]!, channels[1]!, channels[2]!, alpha]
    }
    let effectiveBackground: [number, number, number, number] = [0, 0, 0, 0]
    for (let node: Element | null = element; node !== null; node = node.parentElement) {
      effectiveBackground = over(effectiveBackground, parse(getComputedStyle(node).backgroundColor))
    }
    effectiveBackground = over(effectiveBackground, [255, 255, 255, 1])
    const foreground = parse(getComputedStyle(element).color)
    const luminance = (rgba: number[]) => {
      const channels = rgba.slice(0, 3).map((channel) => {
        const normalized = channel! / 255
        return normalized <= 0.04045 ? normalized / 12.92 : ((normalized + 0.055) / 1.055) ** 2.4
      })
      return 0.2126 * channels[0]! + 0.7152 * channels[1]! + 0.0722 * channels[2]!
    }
    const foregroundLuminance = luminance(foreground)
    const backgroundLuminance = luminance(effectiveBackground)
    const style = getComputedStyle(element)
    return {
      color: style.color,
      background: style.backgroundColor,
      border: style.borderColor,
      contrast: (Math.max(foregroundLuminance, backgroundLuminance) + 0.05)
        / (Math.min(foregroundLuminance, backgroundLuminance) + 0.05),
    }
  })
}

async function expectAccessible(locator: Locator, threshold = 4.5): Promise<RenderedControl> {
  const value = await rendered(locator)
  expect(value.contrast).toBeGreaterThanOrEqual(threshold)
  return value
}

async function expectNoInlineControlColors(locator: Locator): Promise<void> {
  expect(await locator.evaluate((element) => {
    const style = (element as HTMLElement).style
    return { color: style.color, background: style.background, backgroundColor: style.backgroundColor, borderColor: style.borderColor }
  })).toEqual({ color: '', background: '', backgroundColor: '', borderColor: '' })
}

async function expectHoverChange(locator: Locator): Promise<void> {
  const before = await rendered(locator)
  await locator.hover()
  const after = await rendered(locator)
  expect(after.background).not.toBe(before.background)
  expect(after.contrast).toBeGreaterThanOrEqual(4.5)
}

async function openMode(page: Page): Promise<void> {
  const trigger = page.getByRole('button', { name: /Mode:/ })
  if (await trigger.getAttribute('aria-expanded') !== 'true') await trigger.click()
}

async function openSpawn(page: Page): Promise<Locator> {
  const canvas = (await page.locator('#c').boundingBox())!
  await page.mouse.click(canvas.x + canvas.width * 0.5, canvas.y + canvas.height * 0.5, { button: 'right' })
  return page.locator('.vpa-spawn-column').getByRole('button', { name: 'λ term…', exact: true })
}

async function proofBodyPoint(page: Page): Promise<{ x: number; y: number }> {
  const canvas = (await page.locator('#c').boundingBox())!
  const local = await page.evaluate(() => {
    const view = window.__vpaDebug!.view()
    const body = window.__vpaDebug!.bodies().find((candidate) => candidate.kind === 'term')!
    return { x: body.x * view.scale + view.offsetX, y: body.y * view.scale + view.offsetY }
  })
  return { x: canvas.x + local.x, y: canvas.y + local.y }
}

test('Manuscript and Slate render accessible, distinct controls across app mount boundaries', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const utilities = page.getByRole('button', { name: 'Utilities', exact: true })
  const lightNavigation = await expectAccessible(utilities)
  await utilities.click()
  const themeButton = page.getByRole('button', { name: /Theme:/ })
  await expectAccessible(themeButton)
  await themeButton.click()
  await expect(page.locator('html')).toHaveAttribute('data-color-mode', 'dark')
  const darkNavigation = await expectAccessible(utilities)
  expect(darkNavigation.color).not.toBe(lightNavigation.color)
  expect(darkNavigation.background).not.toBe(lightNavigation.background)
  await expectHoverChange(utilities)
  await expectNoInlineControlColors(utilities)

  await utilities.click()
  const spawnRow = await openSpawn(page)
  await expectAccessible(spawnRow)
  await expectHoverChange(spawnRow)
  await expectNoInlineControlColors(spawnRow)
  await spawnRow.click()
  await page.getByLabel('Lambda term to spawn').fill('\\x. x')
  await page.getByLabel('Lambda term to spawn').press('Enter')

  await openMode(page)
  await page.getByRole('button', { name: 'Prove forward', exact: true }).click()
  await expectAccessible(page.locator('.vpa-temporal-undo'))
  await expectAccessible(page.locator('.vpa-temporal-redo'))
  const body = await proofBodyPoint(page)
  await page.mouse.click(body.x, body.y)
  await page.mouse.click(body.x, body.y, { button: 'right' })
  const proofAction = page.locator('.vpa-proof-menu').getByRole('button', { name: 'Wrap in a double cut', exact: true })
  await expectAccessible(proofAction)
  await expectHoverChange(proofAction)
  await expectNoInlineControlColors(proofAction)
  await page.keyboard.press('Escape')

  await page.getByRole('button', { name: 'Return to editing', exact: true }).click()
  await openMode(page)
  await page.getByRole('button', { name: 'Set goal LHS', exact: true }).click()
  await page.getByRole('button', { name: 'Set goal RHS', exact: true }).click()
  await page.getByRole('button', { name: 'Prove fixed sides', exact: true }).click()
  const declare = page.locator('.vpa-fixed-side-declare')
  await expect(declare).toBeEnabled()
  await expectAccessible(declare)
  await expectNoInlineControlColors(declare)
})

test('relation workspace default, primary, and disabled controls follow both themes', async ({ page }) => {
  await page.goto('/test/relation-workspace.html')
  await page.waitForFunction(() => window.relationWorkspaceFixture !== undefined)
  await page.evaluate(() => {
    window.relationWorkspaceFixture.setTheme('light')
    window.relationWorkspaceFixture.mount('abstract')
  })
  const cancel = page.getByRole('button', { name: 'Cancel', exact: true })
  const primary = page.getByRole('button', { name: 'Abstract', exact: true })
  const lightCancel = await expectAccessible(cancel)
  const lightPrimary = await expectAccessible(primary)
  await page.evaluate(() => window.relationWorkspaceFixture.setTheme('dark'))
  const darkCancel = await expectAccessible(cancel)
  const darkPrimary = await expectAccessible(primary)
  expect(darkCancel.background).not.toBe(lightCancel.background)
  expect(darkPrimary.background).not.toBe(lightPrimary.background)
  await expectHoverChange(primary)
  await expectNoInlineControlColors(cancel)
  await expectNoInlineControlColors(primary)

  await page.evaluate(() => window.relationWorkspaceFixture.mountAbstractionScenario('invalid-ports'))
  const disabled = page.locator('.vpa-control-primary')
  await expect(disabled).toBeDisabled()
  await expectAccessible(disabled, 3)
  await expectNoInlineControlColors(disabled)
})
