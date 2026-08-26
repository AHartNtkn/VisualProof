import { expect, type Page } from '@playwright/test'
import { readFile } from 'node:fs/promises'
import { resolve } from 'node:path'
import { test } from './zero-signature-fixture'
import { DARK, LIGHT } from '../src/view/paint'
import { formulaToDiagram } from '../src/formula'
import { loadTheory } from '../src/kernel/proof/store'
import { mkReplay } from '../src/app/replay'
import { scene3 } from '../src/view3d/scene'
import { FOV_DEG, eyeOf, fitPose } from '../src/view3d/camera'
import { cross3, dot3, norm3, sub3 } from '../src/view3d/vec3'

test('a normally loaded Lambda proof remains rendered and pickable in 3D', async ({ page }) => {
  const lambdaFile = resolve('examples/lambda.json')
  const loaded = loadTheory(JSON.parse(await readFile(lambdaFile, 'utf8')))
  const expectedDiagram = mkReplay('LambdaWorkflow', loaded.ctx).diagramAt(1)
  const expectedScene = scene3(expectedDiagram)
  const lambdaStrokes = expectedScene.entities.filter((entity) => entity.kind === 'lambda')
  expect(lambdaStrokes.length).toBeGreaterThan(0)

  await page.goto('/?debug')
  await page.waitForFunction(() => window.__vpaDebug !== undefined)
  await page.locator('#open-file-input').setInputFiles(lambdaFile)
  await page.locator('#library')
    .getByRole('button', { name: '▸ lambda.json', exact: true }).click()
  await page.locator('#library').locator('.vpa-lib-detail')
    .filter({ hasText: 'LambdaWorkflow' })
    .getByRole('button', { name: '▶ Replay', exact: true })
    .click()
  await page.keyboard.press('ArrowRight')
  await expect.poll(() => page.evaluate(() => window.__vpaDebug!.replay().k)).toBe(1)

  await page.getByRole('button', { name: 'Utilities', exact: true }).click()
  await page.getByRole('button', { name: '3D view', exact: true }).click()
  const canvas3 = page.locator('canvas[data-view3]')
  await expect(canvas3).toBeVisible()
  await page.waitForTimeout(900)

  const box = await canvas3.boundingBox()
  if (box === null) throw new Error('the 3D Lambda canvas has no bounding box')
  const aspect = box.width / box.height
  const pose = fitPose(expectedScene.center, expectedScene.radius, aspect)
  const eye = eyeOf(pose)
  const fwd = norm3(sub3(pose.target, eye))
  const right = norm3(cross3(fwd, { x: 0, y: 1, z: 0 }))
  const up = cross3(right, fwd)
  const tanHalf = Math.tan((FOV_DEG * Math.PI) / 360)
  const project = (point: { x: number; y: number; z: number }) => {
    const d = sub3(point, eye)
    const z = dot3(d, fwd)
    return {
      x: box.x + ((dot3(d, right) / z / (tanHalf * aspect)) + 1) / 2 * box.width,
      y: box.y + (1 - dot3(d, up) / z / tanHalf) / 2 * box.height,
    }
  }
  const candidates = lambdaStrokes.flatMap((stroke) => stroke.pts.slice(1).map((point, index) => {
    const before = stroke.pts[index]!
    return project({
      x: (before.x + point.x) / 2,
      y: (before.y + point.y) / 2,
      z: (before.z + point.z) / 2,
    })
  }))
  const wrap = page.locator('div[data-view3-hover]')
  let picked = ''
  let pickedPoint = candidates[0]!
  for (const candidate of candidates) {
    await page.mouse.move(candidate.x, candidate.y)
    await page.waitForTimeout(35)
    const hover = (await wrap.getAttribute('data-view3-hover')) ?? ''
    if (hover.startsWith('t:')) {
      picked = hover
      pickedPoint = candidate
      break
    }
  }
  expect(picked).toMatch(/^t:/u)
  await page.mouse.click(pickedPoint.x, pickedPoint.y)
  await expect.poll(async () => (await wrap.getAttribute('data-view3-focus')) ?? '')
    .toBe(picked)
})

test('3D view mounts, renders the trunk, reports hover, and unmounts', async ({ page }) => {
  await page.goto('/')
  await page.getByRole('button', { name: 'Utilities' }).click()
  await page.getByRole('button', { name: '3D view' }).click()

  const canvas3 = page.locator('canvas[data-view3]')
  await expect(canvas3).toBeVisible()
  await expect(page.locator('#c')).toBeHidden()

  // Rendered content: count pixels that differ from the background.
  // (render.ts sets preserveDrawingBuffer so the buffer is readable.)
  await page.waitForTimeout(300)
  const inkCount = await canvas3.evaluate((c) => {
    const el = c as HTMLCanvasElement
    const off = document.createElement('canvas')
    off.width = el.width
    off.height = el.height
    const ctx = off.getContext('2d')
    if (ctx === null) throw new Error('no 2d context for readback')
    ctx.drawImage(el, 0, 0)
    const img = ctx.getImageData(0, 0, off.width, off.height).data
    const bg = [img[0], img[1], img[2]] as const
    let n = 0
    for (let i = 0; i < img.length; i += 4) {
      const dr = Math.abs(img[i]! - bg[0]!) + Math.abs(img[i + 1]! - bg[1]!) + Math.abs(img[i + 2]! - bg[2]!)
      if (dr > 30) n++
    }
    return n
  })
  expect(inkCount).toBeGreaterThan(50)

  // Hover: the empty sheet's trunk is a vertical line through the view center.
  const box = (await canvas3.boundingBox())!
  const wrap = page.locator('div[data-view3-hover]')
  let hover = ''
  let lastHoverX = 0
  let lastHoverY = 0
  for (let f = 0.25; f <= 0.75 && hover === ''; f += 0.05) {
    lastHoverX = box.x + box.width / 2
    lastHoverY = box.y + box.height * f
    await page.mouse.move(lastHoverX, lastHoverY)
    await page.waitForTimeout(50)
    hover = (await wrap.getAttribute('data-view3-hover')) ?? ''
  }
  expect(hover).toMatch(/^b:/)

  // Click-to-focus: clicking the hovered branch sets the orbit focus to it.
  await page.mouse.click(lastHoverX, lastHoverY)
  await page.waitForTimeout(100)
  expect((await wrap.getAttribute('data-view3-focus')) ?? '').toMatch(/^b:/)

  // Toggle back.
  await page.getByRole('button', { name: '2D view' }).click()
  await expect(page.locator('canvas[data-view3]')).toHaveCount(0)
  await expect(page.locator('#c')).toBeVisible()
})

test.describe('pip color fidelity', () => {
  // A pip disc is only ~5 CSS px across at the fitted camera; doubling the
  // device pixel ratio doubles its device-pixel size so the disc has a flat
  // interior whose exact center pixel is pure disc color, measurable without
  // rim or halo contamination.
  test.use({ deviceScaleFactor: 2, viewport: { width: 1280, height: 720 } })

  // A diagram whose identity nodes sit on relation wires (the ∀-bound P Q R
  // loose ends) and on the ι-order x wire — every pip color class.
  const FORMULA = '∀ P Q R : i → o. ∀ x. P(x) ∧ Q(x) ∧ R(x)'

  /** Opens FORMULA in the 3D view (optionally after switching to the dark
      theme) and asserts every identity pip's disc-core pixel matches one of
      the scene's two legitimate pip colors. */
  const assertPipCores = async (page: Page, theme: 'light' | 'dark'): Promise<void> => {
    await page.goto('/')
    await page.getByRole('button', { name: /Mode: Edit/ }).click()
    await page.getByRole('button', { name: 'Formula…', exact: true }).click()
    const form = page.getByRole('dialog')
    await form.getByLabel('Formula to diagram').fill(FORMULA)
    await form.getByRole('button', { name: 'Create diagram', exact: true }).click()
    await expect(form).toBeHidden()

    await page.getByRole('button', { name: 'Utilities' }).click()
    if (theme === 'dark') {
      await page.getByRole('button', { name: /^Theme: / }).click()
      await expect(page.getByRole('button', { name: `Theme: ${DARK.name}`, exact: true })).toBeVisible()
    }
    await page.getByRole('button', { name: '3D view' }).click()
    const canvas3 = page.locator('canvas[data-view3]')
    await expect(canvas3).toBeVisible()
    await page.waitForTimeout(900) // camera fit + first frames

    // Locate the identity pips deterministically: the shell replaces the
    // diagram with formulaToDiagram(FORMULA) verbatim and mountView3 frames
    // it with fitPose, so rebuilding the scene here and projecting through
    // the same camera math yields the exact on-screen pip centers.
    const box = (await canvas3.boundingBox())!
    const scene = scene3(formulaToDiagram(FORMULA))
    const aspect = box.width / box.height
    const pose = fitPose(scene.center, scene.radius, aspect)
    const eye = eyeOf(pose)
    const fwd = norm3(sub3(pose.target, eye))
    const right = norm3(cross3(fwd, { x: 0, y: 1, z: 0 }))
    const up = cross3(right, fwd)
    const tanHalf = Math.tan((FOV_DEG * Math.PI) / 360)
    const pips = scene.entities.flatMap((e) => (e.kind === 'pip' ? [e] : []))
    expect(pips.length, 'scene has no identity pips — the fixture formula must produce identity nodes').toBeGreaterThan(0)
    const centers = pips.map((p) => {
      const d = sub3(p.pos, eye)
      const z = dot3(d, fwd)
      return {
        key: p.key,
        x: Math.round(((dot3(d, right) / z / (tanHalf * aspect)) + 1) / 2 * box.width),
        y: Math.round((1 - dot3(d, up) / z / tanHalf) / 2 * box.height),
      }
    })
    // The legitimate pip colors in this scene: the relation-order hue ladder
    // rung shared by P/Q/R and the theme's base wire color (the ι wire).
    // Both rasterized by the same canvas-2d path discTexture uses, so the
    // readback must match them exactly up to driver rounding.
    const th = theme === 'dark' ? DARK : LIGHT
    const cssColors = [`hsl(268, 48%, ${th.relationHueLightness}%)`, th.wire]
    const measured = await canvas3.evaluate((c, args) => {
      const el = c as HTMLCanvasElement
      const off = document.createElement('canvas')
      off.width = el.width
      off.height = el.height
      const ctx = off.getContext('2d')
      if (ctx === null) throw new Error('no 2d context for readback')
      ctx.drawImage(el, 0, 0)
      const img = ctx.getImageData(0, 0, off.width, off.height).data
      const sx = el.width / el.clientWidth
      const sy = el.height / el.clientHeight
      const cssToRgb = (color: string): [number, number, number] => {
        const cc = document.createElement('canvas')
        cc.width = cc.height = 1
        const cctx = cc.getContext('2d')!
        cctx.fillStyle = color
        cctx.fillRect(0, 0, 1, 1)
        const d = cctx.getImageData(0, 0, 1, 1).data
        return [d[0]!, d[1]!, d[2]!]
      }
      const pixel = (px: number, py: number): [number, number, number] => {
        const i = (py * off.width + px) * 4
        return [img[i]!, img[i + 1]!, img[i + 2]!]
      }
      return {
        cores: args.centers.map((p) => pixel(Math.round(p.x * sx), Math.round(p.y * sy))),
        legit: args.cssColors.map(cssToRgb),
      }
    }, { centers, cssColors })

    for (const [i, core] of measured.cores.entries()) {
      const dist = measured.legit.map((col) => Math.max(
        Math.abs(core[0]! - col[0]!), Math.abs(core[1]! - col[1]!), Math.abs(core[2]! - col[2]!),
      ))
      expect(
        Math.min(...dist),
        `${theme} pip ${centers[i]!.key} at (${centers[i]!.x},${centers[i]!.y}) core rgb(${core.join(',')}) ` +
        `matches neither the relation hue rgb(${measured.legit[0]!.join(',')}) nor the base wire ` +
        `rgb(${measured.legit[1]!.join(',')}) — rendering must not shift the disc color`,
      ).toBeLessThanOrEqual(16)
    }
  }

  test('dark-mode identity pips keep their wire color at the disc core', async ({ page }) => {
    test.setTimeout(90_000)
    await assertPipCores(page, 'dark')
  })

  test('light-mode identity pips keep their wire color at the disc core', async ({ page }) => {
    test.setTimeout(90_000)
    await assertPipCores(page, 'light')
  })
})
