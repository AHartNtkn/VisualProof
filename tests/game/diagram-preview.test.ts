import { chromium, type Browser } from '@playwright/test'
import { resolve } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'
import { createServer, type ViteDevServer } from 'vite'

const repositoryRoot = resolve(import.meta.dirname, '../..')
let browser: Browser | undefined
let server: ViteDevServer | undefined

afterEach(async () => {
  await browser?.close()
  browser = undefined
  await server?.close()
  server = undefined
})

describe('diagram preview', () => {
  it('renders supplied blank and nested diagrams as distinct visible images', async () => {
    // Mutation caught: a canned, blank, transparent, or input-insensitive preview.
    server = await createServer({
      root: repositoryRoot,
      logLevel: 'silent',
      server: {
        host: '127.0.0.1',
        port: 0,
        watch: null,
      },
      plugins: [{
        name: 'diagram-preview-test-page',
        configureServer(vite) {
          vite.middlewares.use('/diagram-preview-test', (_request, response) => {
            response.statusCode = 200
            response.setHeader('content-type', 'text/html')
            response.end('<!doctype html><canvas id="blank" width="240" height="150"></canvas><canvas id="nested" width="240" height="150"></canvas>')
          })
        },
      }],
    })
    await server.listen()
    const baseUrl = server.resolvedUrls?.local[0]
    if (baseUrl === undefined) throw new Error('Vite did not expose the preview test page')

    browser = await chromium.launch({ headless: true })
    const page = await browser.newPage()
    await page.goto(`${baseUrl}diagram-preview-test`)
    const result = await page.evaluate(async (base) => {
      const load = (path: string): Promise<Record<string, any>> => (
        window.eval(`import(${JSON.stringify(`${base}${path}`)})`) as Promise<Record<string, any>>
      )
      const [{ renderDiagramPreview }, { DiagramBuilder }, { snapshotFromDiagram }] = await Promise.all([
        load('game/diagram-preview.ts'),
        load('src/kernel/diagram/builder.ts'),
        load('src/game/diagram-snapshot.ts'),
      ])
      const blankBuilder = new DiagramBuilder()
      const nestedBuilder = new DiagramBuilder()
      const outer = nestedBuilder.cut(nestedBuilder.root)
      nestedBuilder.cut(outer)
      const blank = document.querySelector<HTMLCanvasElement>('#blank')!
      const nested = document.querySelector<HTMLCanvasElement>('#nested')!
      renderDiagramPreview(blank, snapshotFromDiagram(blankBuilder.build()))
      renderDiagramPreview(nested, snapshotFromDiagram(nestedBuilder.build()))
      const visiblePixels = (canvas: HTMLCanvasElement): number => {
        const pixels = canvas.getContext('2d')!.getImageData(0, 0, canvas.width, canvas.height).data
        let count = 0
        for (let index = 3; index < pixels.length; index += 4) {
          if (pixels[index] !== 0) count += 1
        }
        return count
      }
      return {
        blankPixels: visiblePixels(blank),
        nestedPixels: visiblePixels(nested),
        blankImage: blank.toDataURL(),
        nestedImage: nested.toDataURL(),
      }
    }, baseUrl)

    expect(result.blankPixels).toBeGreaterThan(0)
    expect(result.nestedPixels).toBeGreaterThan(0)
    expect(result.nestedImage).not.toBe(result.blankImage)
  })
})
