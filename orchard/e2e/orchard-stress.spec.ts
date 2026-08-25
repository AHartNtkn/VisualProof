import { expect, test } from '@playwright/test'

type StressRow = {
  trees: number
  entities: number
  buildMs: number
  fps: number
  frameMs: number
  drawCalls: number
  geometries: number
}

const enabled = process.env['ORCHARD_STRESS'] === '1'
const requestedCounts = (process.env['ORCHARD_STRESS_COUNTS'] ?? '10,50,100,250,500,1000,2000')
  .split(',')
  .map(Number)
  .filter((count) => Number.isInteger(count) && count > 0)
if (requestedCounts.length === 0) throw new Error('ORCHARD_STRESS_COUNTS must contain at least one positive integer')

test.skip(!enabled, 'machine-specific stress sweep; run npm run stress:orchard')

test('measures separate proof-tree rendering across increasing counts', async ({ page }) => {
  test.setTimeout(20 * 60_000)
  await page.goto(`/?trees=${requestedCounts[0]}`)
  const orchard = page.locator('[data-orchard]')
  await expect(orchard).toHaveAttribute('data-ready', 'true', { timeout: 12 * 60_000 })

  const gpu = await page.evaluate(() => {
    const canvas = document.querySelector('canvas')
    const gl = canvas?.getContext('webgl2') ?? canvas?.getContext('webgl')
    const extension = gl?.getExtension('WEBGL_debug_renderer_info')
    return {
      vendor: extension === null || extension === undefined ? 'unavailable' : String(gl?.getParameter(extension.UNMASKED_VENDOR_WEBGL)),
      renderer: extension === null || extension === undefined ? 'unavailable' : String(gl?.getParameter(extension.UNMASKED_RENDERER_WEBGL)),
    }
  })
  const rows: StressRow[] = []
  for (const count of requestedCounts) {
    if (await orchard.getAttribute('data-tree-count') !== String(count)) {
      await page.getByRole('spinbutton', { name: 'Tree count', exact: true }).fill(String(count))
      await page.getByRole('button', { name: 'Apply tree count' }).click()
      await expect(orchard).toHaveAttribute('data-tree-count', String(count), { timeout: 12 * 60_000 })
    }
    await page.waitForTimeout(2500)
    const numericText = async (selector: string): Promise<number> => {
      const text = await page.locator(selector).textContent()
      return Number((text ?? '').replaceAll(',', '').replace(/[^0-9.]/g, ''))
    }
    rows.push({
      trees: count,
      entities: Number(await orchard.getAttribute('data-entity-count')),
      buildMs: await numericText('[data-build-ms]'),
      fps: await numericText('[data-fps]'),
      frameMs: await numericText('[data-frame-ms]'),
      drawCalls: await numericText('dd[data-draw-calls]'),
      geometries: await numericText('[data-geometries]'),
    })
    expect(await orchard.getAttribute('data-instanced-count')).toBe('0')
  }
  console.log(`ORCHARD_STRESS_RESULTS ${JSON.stringify({ gpu, rows })}`)
})
