import { expect, test } from '@playwright/test'
import { mkdirSync, readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import type { SavedTree } from '../world'

type StressRow = {
  mode: 'game' | 'raw'
  trees: number
  visible: number
  resident: number
  full: number
  reduced: number
  marker: number
  culled: number
  pendingRepresentations: number
  pointLights: number
  entities: number
  buildMs: number
  settleMs: number
  frameSamples: number
  generation: number
  fps: number
  frameMs: number
  p95FrameMs: number
  drawCalls: number
  geometries: number
}

type StressTimeout = Pick<StressRow,
  'mode' | 'trees' | 'visible' | 'resident' | 'full' | 'reduced' | 'marker' | 'culled'
  | 'pendingRepresentations' | 'pointLights' | 'frameSamples' | 'generation'>

const enabled = process.env['ORCHARD_STRESS'] === '1'
const modeValue = process.env['ORCHARD_STRESS_MODE'] ?? 'game'
if (modeValue !== 'game' && modeValue !== 'raw') {
  throw new Error(`ORCHARD_STRESS_MODE must be "game" or "raw"; received ${JSON.stringify(modeValue)}`)
}
const requestedMode: StressRow['mode'] = modeValue
const requestedCounts = (process.env['ORCHARD_STRESS_COUNTS'] ?? '10,50,100,250,500,1000,2000')
  .split(',')
  .map(Number)
  .filter((count) => Number.isInteger(count) && count > 0)
if (requestedCounts.length === 0) throw new Error('ORCHARD_STRESS_COUNTS must contain at least one positive integer')
const REPRESENTATION_TIMEOUT_MS = 10 * 60_000
const READINESS_TIMEOUT_MS = 12 * 60_000
const STEADY_FRAME_COUNT = 60
const STEADY_FRAME_TIMEOUT_MS = 5 * 60_000
const PER_ROW_OVERHEAD_MS = 60_000
const PER_ROW_TIMEOUT_MS = READINESS_TIMEOUT_MS + REPRESENTATION_TIMEOUT_MS
  + STEADY_FRAME_TIMEOUT_MS + PER_ROW_OVERHEAD_MS

test.skip(!enabled, 'machine-specific stress sweep; run npm run stress:orchard')

test(`measures ${requestedMode} rendering across increasing counts`, async ({ page }) => {
  test.setTimeout(requestedCounts.length * PER_ROW_TIMEOUT_MS + PER_ROW_OVERHEAD_MS)
  const pageErrors: Error[] = []
  page.on('pageerror', (error) => pageErrors.push(error))
  const orchard = page.locator('[data-orchard]')
  const generation = async (name: 'transition-generation' | 'settled-generation'): Promise<number> => {
    const value = Number(await orchard.getAttribute(`data-${name}`))
    if (!Number.isInteger(value) || value < 0) throw new Error(`data-${name} is not a generation: ${value}`)
    return value
  }
  let gpu: { vendor: string, renderer: string } | undefined
  const rows: StressRow[] = []
  for (const count of requestedCounts) {
    const settleStarted = performance.now()
    let targetGeneration: number
    if (requestedMode === 'raw' || rows.length === 0) {
      await page.goto(`/?trees=${count}`)
      await expect(orchard).toHaveAttribute('data-ready', 'true', { timeout: READINESS_TIMEOUT_MS })
      const initialGeneration = await generation('transition-generation')
      await page.getByRole('radio', {
        name: requestedMode === 'game' ? 'Game LOD' : 'Raw full detail',
      }).check()
      targetGeneration = requestedMode === 'raw' ? initialGeneration + 1 : initialGeneration
      await expect(orchard).toHaveAttribute('data-transition-generation', String(targetGeneration))
      await expect(orchard).toHaveAttribute('data-render-mode', requestedMode)
      gpu ??= await page.evaluate(() => {
        const canvas = document.querySelector('canvas')
        const gl = canvas?.getContext('webgl2') ?? canvas?.getContext('webgl')
        const extension = gl?.getExtension('WEBGL_debug_renderer_info')
        return {
          vendor: extension === null || extension === undefined ? 'unavailable' : String(gl?.getParameter(extension.UNMASKED_VENDOR_WEBGL)),
          renderer: extension === null || extension === undefined ? 'unavailable' : String(gl?.getParameter(extension.UNMASKED_RENDERER_WEBGL)),
        }
      })
    } else {
      const previousGeneration = await generation('transition-generation')
      await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill(String(count))
      await page.getByRole('button', { name: 'Apply tree count' }).click()
      targetGeneration = previousGeneration + 1
      await expect(orchard).toHaveAttribute('data-transition-generation', String(targetGeneration))
      await expect(orchard).toHaveAttribute('data-tree-count', String(count), { timeout: 12 * 60_000 })
    }
    try {
      await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: REPRESENTATION_TIMEOUT_MS })
    } catch (error) {
      const timeout = await orchard.evaluate((element, mode): StressTimeout => {
        const dataset = (element as HTMLElement).dataset
        const number = (name: string): number => Number(dataset[name])
        return {
          mode,
          trees: number('logicalCount'),
          visible: number('visibleCount'),
          resident: number('residentCount'),
          full: number('fullCount'),
          reduced: number('reducedCount'),
          marker: number('markerCount'),
          culled: number('culledCount'),
          pendingRepresentations: number('pendingRepresentations'),
          pointLights: number('pointLightCount'),
          frameSamples: number('frameSampleCount'),
          generation: number('transitionGeneration'),
        }
      }, requestedMode)
      console.log(`ORCHARD_STRESS_TIMEOUT ${JSON.stringify(timeout)}`)
      throw error
    }
    const settleMs = performance.now() - settleStarted
    await expect.poll(async () => orchard.evaluate((element) => {
      const dataset = (element as HTMLElement).dataset
      return {
        frameSamples: Number(dataset['frameSampleCount']),
        transitionGeneration: Number(dataset['transitionGeneration']),
        settledGeneration: Number(dataset['settledGeneration']),
      }
    }), { timeout: STEADY_FRAME_TIMEOUT_MS }).toEqual({
      frameSamples: STEADY_FRAME_COUNT,
      transitionGeneration: targetGeneration,
      settledGeneration: targetGeneration,
    })
    const row = await orchard.evaluate((element, { mode, settleMs }): StressRow => {
      const dataset = (element as HTMLElement).dataset
      const number = (name: string): number => {
        const value = Number(dataset[name])
        if (!Number.isFinite(value)) throw new Error(`data-${name} is not a finite number: ${dataset[name]}`)
        return value
      }
      return {
        mode,
        trees: number('logicalCount'),
        visible: number('visibleCount'),
        resident: number('residentCount'),
        full: number('fullCount'),
        reduced: number('reducedCount'),
        marker: number('markerCount'),
        culled: number('culledCount'),
        pendingRepresentations: number('pendingRepresentations'),
        pointLights: number('pointLightCount'),
        entities: number('representedProofEntities'),
        buildMs: number('transitionBuildMs'),
        settleMs,
        frameSamples: number('frameSampleCount'),
        generation: number('settledGeneration'),
        fps: number('fps'),
        frameMs: number('averageFrameMs'),
        p95FrameMs: number('p95FrameMs'),
        drawCalls: number('drawCalls'),
        geometries: number('geometries'),
      }
    }, { mode: requestedMode, settleMs })
    expect(row, `${requestedMode} ${count} tree telemetry`).toMatchObject({
      mode: requestedMode,
      trees: count,
      pendingRepresentations: 0,
      pointLights: 0,
      frameSamples: STEADY_FRAME_COUNT,
      generation: targetGeneration,
    })
    expect(row.buildMs).toBeGreaterThan(0)
    expect(row.full + row.reduced + row.marker + row.culled).toBe(row.trees)
    expect(await orchard.getAttribute('data-instanced-count')).toBe('0')
    rows.push(row)
    console.log(`ORCHARD_STRESS_ROW ${JSON.stringify(row)}`)
  }
  expect(pageErrors).toEqual([])
  if (gpu === undefined) throw new Error('stress sweep did not initialize a renderer')
  console.log(`ORCHARD_STRESS_RESULTS ${JSON.stringify({ mode: requestedMode, gpu, rows })}`)
})

const captureDirectory = process.env['ORCHARD_CAPTURE_DIR']

test('captures fixed-camera Game LOD and irregular-placement evidence', async ({ page }) => {
  test.skip(captureDirectory === undefined, 'set ORCHARD_CAPTURE_DIR to capture visual evidence')
  test.setTimeout(12 * 60_000)
  const target = resolve(captureDirectory!)
  mkdirSync(target, { recursive: true })
  await page.setViewportSize({ width: 1280, height: 720 })
  await page.goto('/?trees=10')
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true', { timeout: 12 * 60_000 })
  await page.getByRole('radio', { name: 'Game LOD' }).check()

  for (const count of [10, 100, 1000]) {
    if (await orchard.getAttribute('data-tree-count') !== String(count)) {
      await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill(String(count))
      await page.getByRole('button', { name: 'Apply tree count' }).click()
      await expect(orchard).toHaveAttribute('data-tree-count', String(count), { timeout: 12 * 60_000 })
    }
    await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: 12 * 60_000 })
    await page.waitForTimeout(500)
    await page.screenshot({ path: resolve(target, `game-${count}.png`) })
  }

  const savedWorld = JSON.parse(readFileSync(new URL('../world.json', import.meta.url), 'utf8'))
  savedWorld.trees = savedWorld.trees.slice(0, 3).map((tree: SavedTree, index: number) => ({
    ...tree,
    x: [savedWorld.player.x, 127, -129][index],
    z: [savedWorld.player.z - 18, 0, -129][index],
  }))
  await page.route('**/world.json*', (route) => route.fulfill({ json: savedWorld }))
  await page.goto('/?trees=3')
  await expect(orchard).toHaveAttribute('data-ready', 'true', { timeout: 30_000 })
  await expect(orchard).toHaveAttribute('data-render-mode', 'game')
  await expect(orchard).toHaveAttribute('data-pending-representations', '0', { timeout: 30_000 })
  await page.waitForTimeout(500)
  await page.screenshot({ path: resolve(target, 'game-irregular-boundary-negative.png') })
})
