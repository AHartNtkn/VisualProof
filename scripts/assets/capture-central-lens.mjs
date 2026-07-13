import { mkdir } from 'node:fs/promises'
import { resolve } from 'node:path'
import { chromium } from '@playwright/test'

const [baseUrl, extra] = process.argv.slice(2)
if (baseUrl === undefined || extra !== undefined) {
  throw new Error('usage: npm run assets:capture-lens -- <preview-url>')
}

const target = new URL('/', baseUrl).href
const output = resolve('test-results/central-lens-review')
await mkdir(output, { recursive: true })

const browser = await chromium.launch()
try {
  for (const capture of [
    { name: 'desktop', viewport: { width: 1440, height: 900 } },
    { name: 'compact', viewport: { width: 700, height: 820 } },
  ]) {
    const page = await browser.newPage({ viewport: capture.viewport, reducedMotion: 'reduce' })
    await page.goto(target, { waitUntil: 'networkidle' })
    await page.locator('.curse-lens-stage').waitFor({ state: 'visible' })
    await page.evaluate(async () => {
      await document.fonts.ready
      const images = [...document.querySelectorAll('.curse-decoration')]
        .filter((element) => element instanceof HTMLImageElement)
      await Promise.all(images.map(async (image) => {
        if (!image.complete) await new Promise((accept, reject) => {
          image.addEventListener('load', accept, { once: true })
          image.addEventListener('error', reject, { once: true })
        })
        if (image.naturalWidth <= 0) throw new Error(`decorative image failed to load: ${image.src}`)
      }))
      await new Promise((accept) => requestAnimationFrame(() => requestAnimationFrame(accept)))
    })
    await page.screenshot({ path: resolve(output, `${capture.name}.png`), animations: 'disabled' })
    await page.close()
  }
} finally {
  await browser.close()
}
