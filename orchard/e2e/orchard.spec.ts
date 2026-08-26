import { expect, test } from '@playwright/test'
import { readFileSync } from 'node:fs'
import type { SavedTree } from '../world'

const THREE_FOV_RADIANS = 67 * Math.PI / 180

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

test('shows tiled ground illumination around a nearby irregular placement', async ({ page }) => {
  await page.setViewportSize({ width: 1280, height: 720 })
  const savedWorld = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
  savedWorld.trees = [{
    ...savedWorld.trees[0],
    x: 0,
    z: 64,
  }]
  await page.route('**/world.json*', (route) => route.fulfill({ json: savedWorld }))
  await page.goto('/?trees=1')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  await page.waitForTimeout(500)

  const screenshot = await page.screenshot()
  const samples = await page.evaluate(async (encoded) => {
    const image = new Image()
    image.src = `data:image/png;base64,${encoded}`
    await image.decode()
    const canvas = document.createElement('canvas')
    canvas.width = image.width
    canvas.height = image.height
    const context = canvas.getContext('2d')!
    context.drawImage(image, 0, 0)
    const rgb = (x: number, y: number) => [...context.getImageData(x, y, 1, 1).data.slice(0, 3)]
    return { glow: rgb(700, 370), unlitGround: rgb(1100, 600) }
  }, screenshot.toString('base64'))
  const luminance = (rgb: readonly number[]) => rgb.reduce((sum, channel) => sum + channel, 0)

  expect(luminance(samples.glow)).toBeGreaterThan(luminance(samples.unlitGround) + 15)
})

test('keeps dense overlapping ground illumination translucent', async ({ page }) => {
  await page.setViewportSize({ width: 1280, height: 720 })
  const savedWorld = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
  savedWorld.trees = savedWorld.trees.slice(0, 10).map((tree: SavedTree) => ({ ...tree, x: 0, z: 64 }))
  await page.route('**/world.json*', (route) => route.fulfill({ json: savedWorld }))
  await page.goto('/?trees=10')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  await page.waitForTimeout(500)

  const screenshot = await page.screenshot()
  const samples = await page.evaluate(async (encoded) => {
    const image = new Image()
    image.src = `data:image/png;base64,${encoded}`
    await image.decode()
    const canvas = document.createElement('canvas')
    canvas.width = image.width
    canvas.height = image.height
    const context = canvas.getContext('2d')!
    context.drawImage(image, 0, 0)
    const rgb = (x: number, y: number) => [...context.getImageData(x, y, 1, 1).data.slice(0, 3)]
    return { glow: rgb(700, 370), unlitGround: rgb(1100, 600) }
  }, screenshot.toString('base64'))
  const luminance = (rgb: readonly number[]) => rgb.reduce((sum, channel) => sum + channel, 0)

  expect(luminance(samples.glow)).toBeGreaterThan(luminance(samples.unlitGround) + 15)
  expect(Math.max(...samples.glow)).toBeLessThan(220)
})

test('reports a complete post-drain frame window and transition build CPU', async ({ page }) => {
  test.setTimeout(60_000)
  await page.goto('/?trees=1')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  expect(Number(await orchard.getAttribute('data-transition-build-ms'))).toBeGreaterThan(0)
  await expect.poll(async () => orchard.evaluate((element) => ({
    samples: (element as HTMLElement).dataset['frameSampleCount'],
    transition: (element as HTMLElement).dataset['transitionGeneration'],
    settled: (element as HTMLElement).dataset['settledGeneration'],
  })), { timeout: 30_000 }).toEqual({ samples: '60', transition: '1', settled: '1' })

  const previousGeneration = Number(await orchard.getAttribute('data-transition-generation'))
  await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill('3')
  await page.getByRole('button', { name: 'Apply tree count' }).click()
  await expect(orchard).toHaveAttribute('data-transition-generation', String(previousGeneration + 1))
  await expect(orchard).toHaveAttribute('data-tree-count', '3')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  expect(Number(await orchard.getAttribute('data-frame-sample-count'))).toBeLessThan(60)
  await expect(orchard).toHaveAttribute('data-settled-generation', String(previousGeneration))
  expect(Number(await orchard.getAttribute('data-transition-build-ms'))).toBeGreaterThan(0)
  await expect.poll(async () => orchard.evaluate((element) => ({
    samples: (element as HTMLElement).dataset['frameSampleCount'],
    transition: (element as HTMLElement).dataset['transitionGeneration'],
    settled: (element as HTMLElement).dataset['settledGeneration'],
  })), { timeout: 30_000 }).toEqual({
    samples: '60',
    transition: String(previousGeneration + 1),
    settled: String(previousGeneration + 1),
  })
})

test('requires a rendered generation before a synchronous count transition can settle', async ({ page }) => {
  await page.goto('/?trees=1')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  const previousGeneration = Number(await orchard.getAttribute('data-transition-generation'))
  await expect(orchard).toHaveAttribute('data-residency-snapshot', JSON.stringify({
    observedGeneration: previousGeneration,
    pendingRepresentations: 0,
  }))

  const synchronousState = await orchard.evaluate((element) => {
    const root = element as HTMLElement
    const input = document.querySelector<HTMLInputElement>('#tree-count')!
    input.value = '3'
    input.dispatchEvent(new Event('input', { bubbles: true }))
    document.querySelector<HTMLFormElement>('[data-count-form]')!.requestSubmit()
    return {
      transitionGeneration: root.dataset['transitionGeneration'],
      pendingRepresentations: root.dataset['pendingRepresentations'],
      residencySnapshot: root.dataset['residencySnapshot'],
    }
  })
  expect(synchronousState).toEqual({
    transitionGeneration: String(previousGeneration + 1),
    pendingRepresentations: '0',
    residencySnapshot: JSON.stringify({
      observedGeneration: previousGeneration,
      pendingRepresentations: 0,
    }),
  })
  await expect(orchard).toHaveAttribute('data-residency-snapshot', JSON.stringify({
    observedGeneration: previousGeneration + 1,
    pendingRepresentations: 0,
  }))
})

test('invalidates settled timing when camera work drains within one render frame', async ({ page }) => {
  test.setTimeout(60_000)
  const viewportHeight = 360
  await page.setViewportSize({ width: 800, height: viewportHeight })
  const savedWorld = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
  const tree = savedWorld.trees[0] as SavedTree
  const layout = savedWorld.layouts[tree.layout]
  const projectionScale = layout.bounds.radius * viewportHeight / Math.tan(THREE_FOV_RADIANS / 2)
  const fullPromotionDepth = projectionScale / (140 * 1.15)
  const fullDemotionDepth = projectionScale / (140 * 0.85)
  const transitionDepth = (fullPromotionDepth + fullDemotionDepth - 6 * 3) / 2
  savedWorld.trees = [{
    ...tree,
    x: savedWorld.player.x,
    z: savedWorld.player.z - transitionDepth,
  }]
  await page.route('**/world.json*', (route) => route.fulfill({ json: savedWorld }))
  await page.goto('/?trees=1')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-full-count', '1')
  await expect(orchard).toHaveAttribute('data-frame-sample-count', '60', { timeout: 30_000 })
  const generation = await orchard.getAttribute('data-transition-generation')
  await page.evaluate(() => {
    const root = document.querySelector<HTMLElement>('[data-orchard]')!
    const operationFrames: Array<{ operations: number, pending: number }> = []
    const observer = new MutationObserver(() => {
      const operations = Number(root.dataset['representationOperations'])
      if (operations > 0) operationFrames.push({
        operations,
        pending: Number(root.dataset['pendingRepresentations']),
      })
    })
    observer.observe(root, { attributes: true, attributeFilter: ['data-representation-operations'] })
    ;(window as Window & { orchardOperationFrames?: typeof operationFrames }).orchardOperationFrames = operationFrames
  })

  await page.keyboard.down('s')
  await page.waitForTimeout(3_000)
  await page.keyboard.up('s')
  await expect(orchard).toHaveAttribute('data-reduced-count', '1')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0')
  expect(await page.evaluate(() => (
    window as Window & { orchardOperationFrames?: Array<{ operations: number, pending: number }> }
  ).orchardOperationFrames)).toContainEqual(expect.objectContaining({ operations: 1, pending: 0 }))
  expect(Number(await orchard.getAttribute('data-frame-sample-count'))).toBeLessThan(60)
  await expect(orchard).toHaveAttribute('data-transition-generation', generation!)
  await expect(orchard).toHaveAttribute('data-frame-sample-count', '60', { timeout: 30_000 })
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
  await expect(orchard).toHaveAttribute('data-render-mode', 'game')
  await expect(orchard).toHaveAttribute('data-point-light-count', '0')
  await expect(orchard).toHaveAttribute('data-full-count', /\d+/)
  await expect(orchard).toHaveAttribute('data-reduced-count', /\d+/)
  await expect(orchard).toHaveAttribute('data-marker-count', /\d+/)
  await expect(orchard).toHaveAttribute('data-culled-count', /\d+/)

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
  await expect(page.locator('[data-status]')).toContainText('10 logical')

  const hundredPreset = page.getByRole('button', { name: '100', exact: true })
  await hundredPreset.click()
  await expect(orchard).toHaveAttribute('data-tree-count', '100')
  await expect(countInput).toBeEnabled()
  await expect(countInput).toHaveValue('100')
  await expect(countScale).toHaveValue('100')
  await expect(hundredPreset).toHaveAttribute('aria-pressed', 'true')
  await expect(page.locator('dd[data-fps]')).toHaveText(/^\d+(?:\.\d)?$/)

  expect(Number(await orchard.getAttribute('data-resident-count'))).toBeLessThan(100)
  await page.getByRole('radio', { name: 'Raw full detail' }).check()
  await expect(orchard).toHaveAttribute('data-render-mode', 'raw')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: 30_000 })
  await expect(orchard).toHaveAttribute('data-full-count', '100')
  await expect(orchard).toHaveAttribute('data-point-light-count', '0')
  await page.getByRole('radio', { name: 'Game LOD' }).check()
  await expect(orchard).toHaveAttribute('data-render-mode', 'game')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: 30_000 })
  const gameGeometries = Number(await orchard.getAttribute('data-geometries'))

  await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill('3')
  await page.getByRole('button', { name: 'Apply tree count' }).click()
  await expect(orchard).toHaveAttribute('data-tree-count', '3')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: 30_000 })
  expect(Number(await orchard.getAttribute('data-resident-count'))).toBeLessThanOrEqual(3)
  expect(Number(await orchard.getAttribute('data-geometries'))).toBeLessThan(gameGeometries)
})

test('updates LOD and glow for irregular saved placements without page errors', async ({ page }) => {
  test.setTimeout(45_000)
  const viewportHeight = 360
  await page.setViewportSize({ width: 800, height: viewportHeight })
  const pageErrors: Error[] = []
  page.on('pageerror', (error) => pageErrors.push(error))
  const savedWorld = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
  const transitionTree = savedWorld.trees[0] as SavedTree
  const transitionLayout = savedWorld.layouts[transitionTree.layout]
  const projectionScale = transitionLayout.bounds.radius * viewportHeight / Math.tan(THREE_FOV_RADIANS / 2)
  const fullPromotionDepth = projectionScale / (140 * 1.15)
  const fullDemotionDepth = projectionScale / (140 * 0.85)
  const threeSecondWalk = 6 * 3
  const transitionDepth = (fullPromotionDepth + fullDemotionDepth - threeSecondWalk) / 2
  if (!(transitionDepth <= fullPromotionDepth && transitionDepth + threeSecondWalk >= fullDemotionDepth)) {
    throw new Error('saved layout radius cannot cross the full LOD band in a three-second walk')
  }
  savedWorld.trees = savedWorld.trees.slice(0, 3).map((tree: SavedTree, index: number) => ({
    ...tree,
    x: [savedWorld.player.x, 127, -129][index],
    z: [savedWorld.player.z - transitionDepth, 0, -129][index],
  }))
  await page.route('**/world.json*', (route) => route.fulfill({ json: savedWorld }))
  await page.goto('/?trees=3')

  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true')
  await expect(orchard).toHaveAttribute('data-tree-count', '3')
  await expect(orchard).toHaveAttribute('data-point-light-count', '0')
  await expect(orchard).toHaveAttribute('data-glow-tile-count', '9')
  await expect(orchard).toHaveAttribute('data-full-count', '1')
  await expect(orchard).toHaveAttribute('data-reduced-count', '2')
  await expect(orchard).toHaveAttribute('data-marker-count', '0')
  await expect(orchard).toHaveAttribute('data-culled-count', '0')
  await page.keyboard.down('s')
  await page.waitForTimeout(3_000)
  await page.keyboard.up('s')
  await expect(orchard).toHaveAttribute('data-full-count', '0')
  await expect(orchard).toHaveAttribute('data-reduced-count', '3')
  await expect(orchard).toHaveAttribute('data-marker-count', '0')
  await expect(orchard).toHaveAttribute('data-culled-count', '0')
  expect(pageErrors).toEqual([])
})
