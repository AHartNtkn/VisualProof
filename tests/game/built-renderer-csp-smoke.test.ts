import { chromium, type Browser, type Page } from '@playwright/test'
import { mkdtemp, readFile, readdir, rm } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { build } from 'vite'
import { afterAll, beforeAll, describe, expect, it } from 'vitest'

type RendererProbe = {
  readonly loadSaveCalls: number
  readonly violations: readonly string[]
}

let browser: Browser
let rendererUrl: string
let buildRoot: string
let entryUrls: readonly string[]
let emittedFiles: readonly string[]

beforeAll(async () => {
  const appRoot = resolve('app')
  buildRoot = await mkdtemp(join(tmpdir(), 'cursebreaker-built-renderer-csp-'))
  const outDir = join(buildRoot, 'dist')
  await build({
    root: appRoot,
    logLevel: 'silent',
    build: { outDir, emptyOutDir: true },
  })
  const indexPath = join(outDir, 'index.html')
  const html = await readFile(indexPath, 'utf8')
  entryUrls = [...html.matchAll(
    /<(?:script|link)\b[^>]*\b(?:src|href)="([^"]+)"[^>]*>/g,
  )].map((match) => match[1]!)
  emittedFiles = await readdir(outDir, { recursive: true })
  rendererUrl = `${pathToFileURL(indexPath).href}?debug`
  browser = await chromium.launch({
    headless: true,
    args: ['--allow-file-access-from-files'],
  })
})

afterAll(async () => {
  await browser?.close()
  if (buildRoot !== undefined) await rm(buildRoot, { recursive: true, force: true })
})

const openBuiltRenderer = async (loadMode: 'success' | 'load-error' = 'success'): Promise<{
  readonly page: Page
  readonly pageErrors: string[]
}> => {
  const page = await browser.newPage({ viewport: { width: 1400, height: 900 } })
  const pageErrors: string[] = []
  page.on('pageerror', (error) => pageErrors.push(error.message))
  await page.addInitScript((mode) => {
    const runtimeWindow = window as typeof window & {
      cursebreakerPlatform: {
        loadSave(): Promise<null>
        writeSave(document: unknown): Promise<void>
        setFullscreen(fullscreen: boolean): Promise<boolean>
        requestExit(document: unknown): Promise<void>
        onExitRequested(callback: () => void): () => void
      }
      __builtRendererProbe: { loadSaveCalls: number; violations: string[] }
    }
    const probe = { loadSaveCalls: 0, violations: [] as string[] }
    Object.defineProperty(runtimeWindow, '__builtRendererProbe', { value: probe })
    Object.defineProperty(runtimeWindow, 'cursebreakerPlatform', {
      value: {
        async loadSave() {
          probe.loadSaveCalls += 1
          if (mode === 'load-error') throw new Error('fixture load failure')
          return null
        },
        async writeSave(_document: unknown) {},
        async setFullscreen(fullscreen: boolean) { return fullscreen },
        async requestExit(_document: unknown) {},
        onExitRequested(_callback: () => void) { return () => {} },
      },
    })
    document.addEventListener('securitypolicyviolation', (event) => {
      probe.violations.push(`${event.violatedDirective}: ${event.blockedURI}`)
    })
  }, loadMode)
  await page.goto(rendererUrl)
  if (loadMode === 'success') {
    await page.waitForFunction(() => {
      const runtimeWindow = window as typeof window & { __cursebreakerDebug?: unknown }
      return runtimeWindow.__cursebreakerDebug !== undefined
    })
  }
  return { page, pageErrors }
}

describe('built renderer production CSP', () => {
  it('boots through the preload boundary and applies runtime custom properties', async () => {
    expect(entryUrls.length).toBeGreaterThanOrEqual(2)
    for (const url of entryUrls) {
      expect(url, `built entry URL must resolve beside index.html: ${url}`).not.toMatch(
        /^(?:\/|[a-z][a-z\d+.-]*:)/i,
      )
    }
    expect(emittedFiles.join('\n')).not.toMatch(
      /(?:^|\/)(?:frame|glass|shadow|lever-housing|lever-handle)(?:-[^/]+)?\.png(?:$|\n)/,
    )
    const { page, pageErrors } = await openBuiltRenderer()
    try {
      const csp = await page.locator('meta[http-equiv="Content-Security-Policy"]')
        .getAttribute('content')
      expect(csp).not.toBeNull()
      const directives = new Map(csp!.split(';').map((part) => {
        const [name, ...values] = part.trim().split(/\s+/)
        return [name, values] as const
      }))
      expect(directives.get('style-src')).toEqual(["'self'"])
      expect(directives.get('style-src-attr')).toEqual(["'unsafe-inline'"])
      for (const [name, value] of [
        ['script-src', "'self'"],
        ['connect-src', "'none'"],
        ['object-src', "'none'"],
        ['base-uri', "'none'"],
        ['form-action', "'none'"],
        ['frame-src', "'none'"],
      ] as const) expect(directives.get(name)).toEqual([value])

      const lens = page.locator('.curse-production-lens')
      const before = await lens.evaluate((node) => {
        const element = node as HTMLElement
        const style = getComputedStyle(element)
        return {
          customLeft: style.getPropertyValue('--curse-lens-left').trim(),
          inlineLeft: element.style.getPropertyValue('--curse-lens-left').trim(),
          computedLeft: style.left,
        }
      })
      expect(before.customLeft).toBe(before.inlineLeft)
      expect(Number.parseFloat(before.computedLeft)).toBeCloseTo(
        Number.parseFloat(before.customLeft),
        6,
      )

      await page.setViewportSize({ width: 760, height: 900 })
      await expect.poll(async () => lens.evaluate((node) =>
        getComputedStyle(node).getPropertyValue('--curse-lens-left').trim(),
      )).not.toBe(before.customLeft)
      const after = await lens.evaluate((node) => {
        const element = node as HTMLElement
        const style = getComputedStyle(element)
        return {
          customLeft: style.getPropertyValue('--curse-lens-left').trim(),
          inlineLeft: element.style.getPropertyValue('--curse-lens-left').trim(),
          computedLeft: style.left,
        }
      })
      expect(after.customLeft).toBe(after.inlineLeft)
      expect(Number.parseFloat(after.computedLeft)).toBeCloseTo(
        Number.parseFloat(after.customLeft),
        6,
      )

      const probe = await page.evaluate(() => (
        window as typeof window & { __builtRendererProbe: RendererProbe }
      ).__builtRendererProbe)
      expect(probe.loadSaveCalls).toBe(1)
      expect(probe.violations).toEqual([])
      expect(pageErrors).toEqual([])
    } finally {
      await page.close()
    }
  })

  it('renders an accessible diagnostic instead of an empty black host when startup fails', async () => {
    const { page, pageErrors } = await openBuiltRenderer('load-error')
    try {
      const alert = page.locator('.curse-launch-failure[role="alert"]')
      await expect.poll(() => alert.count()).toBe(1)
      await expect.poll(() => alert.textContent()).toContain('Cursebreaker could not start')
      await expect.poll(() => page.locator('#cursebreaker').getAttribute('data-launch-state'))
        .toBe('failed')
      expect(pageErrors).toEqual([])
    } finally {
      await page.close()
    }
  })
})
