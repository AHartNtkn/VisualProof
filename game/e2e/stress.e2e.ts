import { browser, expect } from '@wdio/globals'
import { describe, it } from 'mocha'
import { attribute, game, loadSlot, numberAttribute, setRenderMode } from './native'

const scenario = process.env['GAME_E2E_SCENARIO'] ?? ''
const match = /^stress-(10|50|100|250|500|1000|2000)$/.exec(scenario)
if (match === null) throw new Error(`stress test requires a standard stress scenario, got '${scenario}'`)
const count = Number(match[1])
const comparesRawRepresentation = count === 10 || count === 2000

async function waitForSettlement(): Promise<void> {
  await browser.waitUntil(async () => {
    return await attribute('pending-representation-count') === '0'
      && await attribute('settled-generation') === await attribute('transition-generation')
  }, { timeout: 12 * 60_000, interval: 100 })
}

function recordDiagnostics(mode: 'game' | 'raw', values: Readonly<Record<string, number>>): void {
  process.stdout.write(`${JSON.stringify({ scenario, mode, ...values })}\n`)
}

describe(`ordinary ${scenario} save`, () => {
  it('loads through the menu and settles in normal game mode', async () => {
    await loadSlot(scenario)
    await waitForSettlement()

    expect(await numberAttribute('logical-count')).toBe(count)
    expect(await numberAttribute('representation-error-count')).toBe(0)
    expect(await attribute('representation-error')).toBe('')
    expect(await numberAttribute('point-light-count')).toBe(0)
    const visible = await numberAttribute('visible-count')
    const resident = await numberAttribute('resident-count')
    const full = await numberAttribute('full-count')
    const reduced = await numberAttribute('reduced-count')
    const marker = await numberAttribute('marker-count')
    const culled = await numberAttribute('culled-count')
    expect(resident).toBe(visible)
    expect(resident).toBe(full + reduced + marker)
    expect(visible + culled).toBe(count)
    recordDiagnostics('game', {
      count,
      visible,
      resident,
      full,
      reduced,
      marker,
      culled,
      p95FrameMs: await numberAttribute('p95-frame-ms'),
      transitionBuildMs: await numberAttribute('transition-build-ms'),
      drawCalls: await numberAttribute('draw-calls'),
      geometries: await numberAttribute('geometries'),
      maxRepresentationOperations: await numberAttribute('max-representation-operations'),
    })

    if (!comparesRawRepresentation) return

    await setRenderMode('raw')
    await expect(game()).toHaveAttribute('data-render-mode', 'raw')
    await waitForSettlement()
    expect(await numberAttribute('logical-count')).toBe(count)
    expect(await numberAttribute('visible-count')).toBe(count)
    expect(await numberAttribute('resident-count')).toBe(count)
    expect(await numberAttribute('full-count')).toBe(count)
    expect(await numberAttribute('reduced-count')).toBe(0)
    expect(await numberAttribute('marker-count')).toBe(0)
    expect(await numberAttribute('culled-count')).toBe(0)
    expect(await numberAttribute('representation-error-count')).toBe(0)
    expect(await numberAttribute('point-light-count')).toBe(0)
    recordDiagnostics('raw', {
      count,
      p95FrameMs: await numberAttribute('p95-frame-ms'),
      transitionBuildMs: await numberAttribute('transition-build-ms'),
      drawCalls: await numberAttribute('draw-calls'),
      geometries: await numberAttribute('geometries'),
      maxRepresentationOperations: await numberAttribute('max-representation-operations'),
    })
  })
})
