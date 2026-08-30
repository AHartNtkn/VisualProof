import { chromium, type Browser } from '@playwright/test'
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { createServer as createTcpServer } from 'node:net'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'
import { createServer, type ViteDevServer } from 'vite'

const repositoryRoot = resolve(import.meta.dirname, '../..')

let browser: Browser | undefined
let server: ViteDevServer | undefined
let fixtureRoot: string | undefined

async function reserveAvailablePort(): Promise<number> {
  return new Promise((resolvePort, rejectPort) => {
    const reservation = createTcpServer()
    reservation.once('error', rejectPort)
    reservation.listen(0, '127.0.0.1', () => {
      const address = reservation.address()
      if (address === null || typeof address === 'string') {
        reservation.close()
        rejectPort(new Error('Could not reserve a TCP port for the Vite fixture'))
        return
      }

      reservation.close((error) => {
        if (error !== undefined) {
          rejectPort(error)
          return
        }
        resolvePort(address.port)
      })
    })
  })
}

function writeEntry(revision: string): void {
  if (fixtureRoot === undefined) {
    throw new Error('Vite watch fixture is not initialized')
  }

  writeFileSync(
    join(fixtureRoot, 'main.ts'),
    `import ordersJson from './game/content/orders.json?raw'

const visits = Number(sessionStorage.getItem('vite-watch-visits') ?? '0') + 1
sessionStorage.setItem('vite-watch-visits', String(visits))
document.body.dataset.visits = String(visits)
document.body.dataset.orders = ordersJson
document.body.dataset.revision = ${JSON.stringify(revision)}
`,
  )
}

afterEach(async () => {
  await browser?.close()
  browser = undefined

  await server?.close()
  server = undefined

  if (fixtureRoot !== undefined) {
    rmSync(fixtureRoot, { recursive: true, force: true })
    fixtureRoot = undefined
  }
})

describe('Vite runtime content watch boundary', () => {
  it(
    'keeps an active browser session when the imported order catalog is persisted',
    async () => {
      fixtureRoot = mkdtempSync(join(tmpdir(), 'orchard-vite-watch-'))
      mkdirSync(join(fixtureRoot, 'game/content'), { recursive: true })
      writeFileSync(
        join(fixtureRoot, 'index.html'),
        '<!doctype html><html><body><script type="module" src="/main.ts"></script></body></html>',
      )
      writeFileSync(
        join(fixtureRoot, 'game/content/orders.json'),
        '{"orders":[{"id":"initial-order"}]}\n',
      )
      writeEntry('initial')

      const port = await reserveAvailablePort()

      server = await createServer({
        configFile: join(repositoryRoot, 'vite.config.ts'),
        root: fixtureRoot,
        logLevel: 'silent',
        server: {
          host: '127.0.0.1',
          port,
          strictPort: true,
        },
      })
      await server.listen()

      const url = server.resolvedUrls?.local[0]
      expect(url).toBeDefined()

      browser = await chromium.launch({ headless: true })
      const page = await browser.newPage()
      await page.goto(url!)
      await expect
        .poll(() => page.locator('body').getAttribute('data-visits'))
        .toBe('1')
      await expect
        .poll(() => page.locator('body').getAttribute('data-orders'))
        .toContain('initial-order')

      writeFileSync(
        join(fixtureRoot, 'game/content/orders.json'),
        '{"orders":[{"id":"persisted-order"}]}\n',
      )
      await new Promise((resolveDelay) => setTimeout(resolveDelay, 750))
      expect(await page.locator('body').getAttribute('data-visits')).toBe('1')
      expect(await page.locator('body').getAttribute('data-orders')).toContain(
        'initial-order',
      )

      writeEntry('ordinary-source-change')
      await expect
        .poll(() => page.locator('body').getAttribute('data-visits'), {
          timeout: 5_000,
        })
        .toBe('2')
      expect(await page.locator('body').getAttribute('data-revision')).toBe(
        'ordinary-source-change',
      )
    },
    15_000,
  )
})
