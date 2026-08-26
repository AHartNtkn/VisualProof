import { expect, test } from '@playwright/test'

test('accumulates overlapping glow contributors into bounded order-independent pixels', async ({ page }) => {
  await page.goto('/?trees=1')

  const pixels = await page.evaluate(async () => {
    const modulePath = '/glow-render.ts'
    const { mountGlowRenderer } = await import(modulePath)
    type AddedMesh = { readonly material: { readonly map: { readonly image: HTMLCanvasElement } } }
    const added: AddedMesh[] = []
    const scene = {
      add(object: unknown) { added.push(object as AddedMesh) },
      remove() {},
    }
    const renderer = mountGlowRenderer(scene, 0)
    const contribution = (id: string, color: string) => ({
      id, x: 64, z: 64, radius: 32, color, opacity: 0.75,
    })
    const render = (contributors: readonly ReturnType<typeof contribution>[]) => {
      renderer.sync([{ key: '0:0', x: 0, z: 0, contributors }])
      const context = added[0]!.material.map.image.getContext('2d')!
      return Array.from(context.getImageData(64, 64, 1, 1).data)
    }

    const single = render([contribution('red', '#ff0000')])
    const doubled = render([contribution('red-1', '#ff0000'), contribution('red-2', '#ff0000')])
    const redGreen = render([contribution('red', '#ff0000'), contribution('green', '#00ff00')])
    const greenRed = render([contribution('green', '#00ff00'), contribution('red', '#ff0000')])
    renderer.dispose()
    return { single, doubled, redGreen, greenRed }
  })

  expect.soft(pixels.doubled[3]).toBeGreaterThan(pixels.single[3]!)
  expect.soft(pixels.doubled[3]).toBe(255)
  expect.soft(pixels.redGreen).toEqual(pixels.greenRed)
  expect.soft(pixels.redGreen[3]).toBe(255)
})

test('renders exact separate tree counts and lets the player walk', async ({ page }) => {
  test.setTimeout(45_000)
  const started = performance.now()
  await page.goto('/?trees=3')

  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true', { timeout: 30_000 })
  expect(performance.now() - started).toBeLessThan(3000)
  await expect(page).toHaveTitle('Orchard Renderer Stress Test')
  await expect(orchard).toHaveAttribute('data-world-version', '2')
  await expect(orchard).toHaveAttribute('data-saved-tree-count', '2000')
  await expect(orchard).toHaveAttribute('data-tree-count', '3')
  await expect(orchard).toHaveAttribute('data-entity-count', '219')
  await expect(orchard).toHaveAttribute('data-instanced-count', '0')

  const countScale = page.getByRole('slider', { name: 'Tree count scale' })
  await expect(countScale).toHaveValue('3')
  await expect(page.getByText('zeroIsNat · step 20')).toBeVisible()
  await expect(page.getByText('Draw calls')).toBeVisible()

  const before = Number(await orchard.getAttribute('data-player-z'))
  await page.keyboard.down('w')
  await page.waitForTimeout(350)
  await page.keyboard.up('w')
  const after = Number(await orchard.getAttribute('data-player-z'))
  expect(after).toBeLessThan(before - 0.5)

  await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill('5')
  await page.getByRole('button', { name: 'Apply tree count' }).click()
  await expect(orchard).toHaveAttribute('data-tree-count', '5')
  await expect(orchard).toHaveAttribute('data-entity-count', '365')
  await expect(orchard).toHaveAttribute('data-instanced-count', '0')

  const countInput = page.getByRole('spinbutton', { name: 'Tree count', exact: true })
  await countScale.fill('10')
  await countScale.dispatchEvent('change')
  await expect(orchard).toHaveAttribute('data-tree-count', '10')
  await expect(countInput).toHaveValue('10')
  await expect(page.locator('[data-status]')).toContainText('10 independent trees · 740 renderer objects')

  const hundredPreset = page.getByRole('button', { name: '100', exact: true })
  await hundredPreset.click()
  await expect(countInput).toBeDisabled()
  await expect(orchard).toHaveAttribute('data-tree-count', '100')
  await expect(countInput).toBeEnabled()
  await expect(countInput).toHaveValue('100')
  await expect(countScale).toHaveValue('100')
  await expect(hundredPreset).toHaveAttribute('aria-pressed', 'true')
  await expect(page.locator('[data-fps]')).toHaveText(/^\d+(?:\.\d)?$/)
})
