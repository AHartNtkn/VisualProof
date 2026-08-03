import { expect, test } from './zero-signature-fixture'

function contrast(color: string, background: string): number {
  const luminance = (value: string): number => {
    const channels = value.match(/\d+(?:\.\d+)?/gu)?.map(Number)
    if (channels === undefined || channels.length < 3) throw new Error(`Expected rgb color, received ${value}`)
    const [red, green, blue] = channels.slice(0, 3).map((channel) => {
      const normalized = channel / 255
      return normalized <= 0.04045 ? normalized / 12.92 : ((normalized + 0.055) / 1.055) ** 2.4
    })
    return 0.2126 * red! + 0.7152 * green! + 0.0722 * blue!
  }
  const [a, b] = [luminance(color), luminance(background)]
  return (Math.max(a, b) + 0.05) / (Math.min(a, b) + 0.05)
}

declare global {
  interface Window {
    __vpaDebug?: {
      nodeCount(): number
      status(): string
      replay(): {
        mode: string
        k: number
        n: number
        meetingIndex: number
        endpointKind: 'lhs' | 'meet' | 'rhs' | 'state'
        label: string
        bodies: number
        foldedRefs: string[]
      }
      interaction(): {
        selected: readonly { kind: 'node' | 'region' | 'wire'; id: string }[]
        pins: string[]
        userZoom: number
      }
      diagram(): {
        nodes: { id: string; kind: string }[]
        wires: { id: string }[]
        regions: { id: string; kind: string }[]
      }
      dispose(): void
    }
  }
}

test('the app boots empty and loads and unloads a zero-signature theory file', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await expect(page.locator('#c')).toBeVisible()
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const library = page.locator('#library')
  await expect(library.getByRole('button', { name: 'Open folder…', exact: true })).toBeVisible()
  await expect(library.getByRole('button', { name: 'Open file…', exact: true })).toBeVisible()
  await expect(library).toContainText('No workspace folder open')
  await expect(page.getByRole('button', { name: /Mode: Edit/ })).toBeVisible()
  await expect(page.locator('#status')).toContainText('EDIT')

  expect(await page.evaluate(() => ({
    nodes: window.__vpaDebug!.nodeCount(),
    status: window.__vpaDebug!.status(),
    interaction: window.__vpaDebug!.interaction(),
  }))).toEqual({
    nodes: 0,
    status: expect.stringContaining('EDIT'),
    interaction: { selected: [], pins: [], userZoom: 1 },
  })

  await page.locator('#open-file-input').setInputFiles(theoryFiles.tiny)
  await expect(library.getByRole('button', {
    name: 'Unload zero-signature.json',
    exact: true,
  })).toBeVisible()
  await library.getByRole('button', { name: '▸ zero-signature.json', exact: true }).click()
  await expect(library).toContainText('StructuralReflexivity')
  await expect(library).toContainText('UnaryWitness')

  await library.getByRole('button', {
    name: 'Unload zero-signature.json',
    exact: true,
  }).click()
  await expect(library).not.toContainText('StructuralReflexivity')
  await expect(page.locator('#status')).toContainText('EDIT')
})

test('formula entry creates a diagram, rejects malformed source, and preserves Edit undo', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.getByRole('button', { name: /Mode: Edit/ }).click()
  const formulaButton = page.getByRole('button', { name: 'Formula…', exact: true })
  await formulaButton.click()
  const form = page.getByRole('dialog')
  await form.getByLabel('Formula to diagram').fill('∀ Z : i → o. ∀ S : i → i → o. (∃ z. Z(z)) ⇒ (∀ z. Z(z) ⇒ (∀ P : i → o. ((∀ n. Z(n) ⇒ P(n)) & (∀ n m. (P(n) & S(n, m)) ⇒ P(m))) ⇒ P(z)))')
  await form.getByRole('button', { name: 'Create diagram', exact: true }).click()

  await expect(form).toBeHidden()
  await expect(formulaButton).toBeFocused()
  const diagramSummary = () => page.evaluate(() => {
    const diagram = window.__vpaDebug!.diagram()
    return {
      cutRegions: diagram.regions.filter((region) => region.kind === 'cut').length,
      atoms: diagram.nodes.filter((node) => node.kind === 'atom').length,
      wires: diagram.wires.length,
    }
  })
  expect(await diagramSummary()).toEqual({
    cutRegions: 22,
    atoms: 8,
    wires: 8,
  })

  await formulaButton.click()
  await form.getByRole('button', { name: 'Cancel', exact: true }).click()
  await expect(form).toBeHidden()
  await expect(formulaButton).toBeFocused()

  await formulaButton.click()
  await page.keyboard.press('Escape')
  await expect(form).toBeHidden()
  await expect(formulaButton).toBeFocused()

  await formulaButton.click()
  const source = form.getByLabel('Formula to diagram')
  await source.fill('')
  await form.getByRole('button', { name: 'Create diagram', exact: true }).click()

  await expect(form.locator('.vpa-formula-error')).toContainText(/line 1, column \d+/)
  await expect(source).toHaveAttribute('aria-invalid', 'true')
  await expect(form).toBeVisible()
  expect(await diagramSummary()).toEqual({
    cutRegions: 22,
    atoms: 8,
    wires: 8,
  })

  await form.getByLabel('Formula to diagram').fill('∀ x. Missing(x)')
  await form.getByRole('button', { name: 'Create diagram', exact: true }).click()

  await expect(form.locator('.vpa-formula-error')).toBeVisible()
  await expect(form.locator('.vpa-formula-error')).toContainText(/line 1, column \d+/)
  expect(await diagramSummary()).toEqual({
    cutRegions: 22,
    atoms: 8,
    wires: 8,
  })

  await page.keyboard.press('Control+z')
  expect(await diagramSummary()).toEqual({
    cutRegions: 0,
    atoms: 0,
    wires: 0,
  })
})

test('formula entry uses explicit readable Dark control colors', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.getByRole('button', { name: /^Theme:/u }).click()
  await expect(page.locator('html')).toHaveAttribute('data-color-mode', 'dark')
  await page.getByRole('button', { name: 'Formula…', exact: true }).click()
  const form = page.getByRole('dialog')
  await form.getByLabel('Formula to diagram').fill('∀ x. Missing(x)')
  await form.getByRole('button', { name: 'Create diagram', exact: true }).click()

  const colors = await form.evaluate((dialog) => {
    const colorOf = (selector: string, property: 'color' | 'backgroundColor'): string => {
      const element = dialog.querySelector(selector)
      if (element === null) throw new Error(`Missing ${selector}`)
      return getComputedStyle(element)[property]
    }
    return {
      panel: getComputedStyle(dialog).backgroundColor,
      label: colorOf('label', 'color'),
      buttonForeground: colorOf('button[type="submit"]', 'color'),
      buttonBackground: colorOf('button[type="submit"]', 'backgroundColor'),
      error: colorOf('.vpa-formula-error', 'color'),
    }
  })

  expect(colors).toEqual({
    panel: 'rgb(31, 36, 42)',
    label: 'rgb(184, 176, 165)',
    buttonForeground: 'rgb(26, 22, 17)',
    buttonBackground: 'rgb(240, 164, 58)',
    error: 'rgb(251, 113, 133)',
  })
  expect(contrast(colors.label, colors.panel)).toBeGreaterThanOrEqual(4.5)
  expect(contrast(colors.buttonForeground, colors.buttonBackground)).toBeGreaterThanOrEqual(4.5)
  expect(contrast(colors.error, colors.panel)).toBeGreaterThanOrEqual(4.5)
})

test('the committed Frege theory loads through the ordinary library path', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const library = page.locator('#library')
  await page.locator('#open-file-input').setInputFiles(theoryFiles.frege)
  await expect(library.getByRole('button', {
    name: 'Unload frege.json',
    exact: true,
  })).toBeVisible()
  await library.getByRole('button', { name: '▸ frege.json', exact: true }).click()
  await expect(library).toContainText('existsProp')
  await expect(library).toContainText('plusComm')
})

test('zeroIsNat replay reaches the declared RHS with its folded nat reference', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const library = page.locator('#library')
  await page.locator('#open-file-input').setInputFiles(theoryFiles.frege)
  await library.getByRole('button', { name: '▸ frege.json', exact: true }).click()
  await library.locator('.vpa-lib-detail').filter({ hasText: 'zeroIsNat' }).evaluate((row) => {
    const nodes = [...row.childNodes]
    const name = nodes.findIndex((node) => node.nodeType === Node.TEXT_NODE
      && node.textContent?.includes('zeroIsNat'))
    const replay = nodes.slice(name + 1).find((node): node is HTMLButtonElement =>
      node instanceof HTMLButtonElement && node.textContent === '▶ Replay')
    replay?.click()
  })
  await expect(page.locator('#status')).toContainText('LHS')

  const rail = page.locator('.vpa-temporal-rail')
  const box = await rail.boundingBox()
  expect(box).not.toBeNull()
  await page.mouse.click(box!.x + box!.width - 1, box!.y + box!.height / 2)

  await expect(page.locator('#status')).toContainText('RHS')
  expect(await page.evaluate(() => window.__vpaDebug!.replay())).toMatchObject({
    mode: 'replay',
    endpointKind: 'rhs',
    foldedRefs: expect.arrayContaining(['nat']),
  })
})

test('the keyboard map exposes the surviving structural shortcuts', async ({ page }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  const map = page.locator('.vpa-keyboard-map')
  await expect(map).toBeHidden()
  await page.getByRole('button', { name: 'Utilities', exact: true }).click()
  await page.getByRole('button', { name: 'Keyboard map', exact: true }).click()
  await expect(map).toBeVisible()
  await expect(map).toContainText('Ctrl+Z undo')
  await expect(map).toContainText('Home fit')
  await expect(map).toContainText('Delete contextual erase')
})

test('an invalid theory file reports a visible library error', async ({ page, theoryFiles }) => {
  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)

  await page.locator('#open-file-input').setInputFiles(theoryFiles.invalid)

  await expect(page.locator('#library')).toContainText('load failed:')
  await expect(page.locator('#library')).toContainText('Unexpected end of JSON input')
  expect(await page.evaluate(() => window.__vpaDebug!.nodeCount())).toBe(0)
})
