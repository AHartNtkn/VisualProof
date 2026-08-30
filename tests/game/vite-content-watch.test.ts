import { chromium, type Browser } from '@playwright/test'
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process'
import {
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs'
import { createServer as createTcpServer } from 'node:net'
import { createServer as createHttpServer, type Server } from 'node:http'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'

const repositoryRoot = resolve(import.meta.dirname, '../..')

let browser: Browser | undefined
let viteProcess: ChildProcessWithoutNullStreams | undefined
let viteOutput = ''
let fixtureRoot: string | undefined
let contentServer: Server | undefined

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
    join(fixtureRoot, 'game/main.ts'),
    `import ordersJson from './content/orders.json?raw'
import tutorialJson from './content/tutorial.json?raw'
import toolsJson from './content/tools.json?raw'

const visits = Number(sessionStorage.getItem('vite-watch-visits') ?? '0') + 1
sessionStorage.setItem('vite-watch-visits', String(visits))
document.body.dataset.visits = String(visits)
document.body.dataset.orders = ordersJson
document.body.dataset.tutorial = tutorialJson
document.body.dataset.tools = toolsJson
document.body.dataset.revision = ${JSON.stringify(revision)}
`,
  )
}

async function startContentServer(): Promise<string> {
  if (fixtureRoot === undefined) throw new Error('Vite watch fixture is not initialized')
  const root = fixtureRoot
  const port = await reserveAvailablePort()
  contentServer = createHttpServer((request, response) => {
    const fileName = request.url === '/__orchard_playtest/content/tutorial'
      ? 'tutorial.json'
      : request.url === '/__orchard_playtest/content/tools'
        ? 'tools.json'
        : undefined
    if (request.method !== 'POST' || fileName === undefined) {
      response.writeHead(404).end()
      return
    }
    const chunks: Buffer[] = []
    request.on('data', (chunk: Buffer) => chunks.push(chunk))
    request.on('end', () => {
      const body = JSON.parse(Buffer.concat(chunks).toString()) as { content: unknown }
      writeFileSync(
        join(root, 'game/content', fileName),
        `${JSON.stringify(body.content, null, 2)}\n`,
      )
      response.writeHead(200, { 'content-type': 'application/json' }).end('null')
    })
  })
  await new Promise<void>((resolveListen, rejectListen) => {
    contentServer!.once('error', rejectListen)
    contentServer!.listen(port, '127.0.0.1', resolveListen)
  })
  return `http://127.0.0.1:${port}`
}

async function waitForVite(url: string): Promise<void> {
  const deadline = Date.now() + 5_000
  while (Date.now() < deadline) {
    if (viteProcess?.exitCode !== null) {
      throw new Error(`Vite exited before becoming ready:\n${viteOutput}`)
    }

    try {
      const response = await fetch(url)
      if (response.ok) {
        return
      }
    } catch {
      // The CLI is still starting.
    }
    await new Promise((resolveDelay) => setTimeout(resolveDelay, 50))
  }

  throw new Error(`Vite did not become ready:\n${viteOutput}`)
}

async function stopVite(): Promise<void> {
  const runningProcess = viteProcess
  viteProcess = undefined
  if (runningProcess === undefined || runningProcess.exitCode !== null) {
    return
  }

  const exited = new Promise<void>((resolveExit) => {
    runningProcess.once('exit', () => resolveExit())
  })
  runningProcess.kill('SIGTERM')
  await Promise.race([
    exited,
    new Promise<void>((resolveTimeout) => setTimeout(resolveTimeout, 2_000)),
  ])
  if (runningProcess.exitCode === null) {
    runningProcess.kill('SIGKILL')
    await exited
  }
}

afterEach(async () => {
  await browser?.close()
  browser = undefined

  await stopVite()
  viteOutput = ''

  if (contentServer !== undefined) {
    await new Promise<void>((resolveClose, rejectClose) => {
      contentServer!.close((error) => error === undefined ? resolveClose() : rejectClose(error))
    })
    contentServer = undefined
  }

  if (fixtureRoot !== undefined) {
    rmSync(fixtureRoot, { recursive: true, force: true })
    fixtureRoot = undefined
  }
})

describe('Vite runtime content watch boundary', () => {
  it(
    'keeps an active browser session when imported authored content is persisted',
    async () => {
      fixtureRoot = mkdtempSync(join(tmpdir(), 'orchard-vite-watch-'))
      mkdirSync(join(fixtureRoot, 'game/content'), { recursive: true })
      symlinkSync(
        join(repositoryRoot, 'node_modules'),
        join(fixtureRoot, 'node_modules'),
        'dir',
      )
      writeFileSync(
        join(fixtureRoot, 'game/index.html'),
        '<!doctype html><html><body><script type="module" src="/main.ts"></script></body></html>',
      )
      writeFileSync(
        join(fixtureRoot, 'game/content/orders.json'),
        '{"orders":[{"id":"initial-order"}]}\n',
      )
      writeFileSync(
        join(fixtureRoot, 'game/content/tutorial.json'),
        '[{"milestoneId":"move","text":"initial tutorial"}]\n',
      )
      writeFileSync(
        join(fixtureRoot, 'game/content/tools.json'),
        '[{"id":"iteration","name":"initial tool","description":"initial description"}]\n',
      )
      writeEntry('initial')
      const contentUrl = await startContentServer()

      const gameConfig = join(repositoryRoot, 'game/vite.config.ts')
      if (existsSync(gameConfig)) {
        copyFileSync(gameConfig, join(fixtureRoot, 'game/vite.config.ts'))
      }

      const port = await reserveAvailablePort()
      const url = `http://127.0.0.1:${port}`
      viteProcess = spawn(
        join(repositoryRoot, 'node_modules/.bin/vite'),
        ['game', '--host', '127.0.0.1', '--port', String(port), '--strictPort'],
        {
          cwd: fixtureRoot,
          env: { ...process.env, NO_COLOR: '1' },
        },
      )
      viteProcess.stdout.on('data', (chunk: Buffer) => {
        viteOutput += chunk.toString()
      })
      viteProcess.stderr.on('data', (chunk: Buffer) => {
        viteOutput += chunk.toString()
      })
      await waitForVite(url)

      browser = await chromium.launch({ headless: true })
      const page = await browser.newPage()
      await page.goto(url)
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

      for (const [document, content] of [
        ['tutorial', [{ milestoneId: 'move', text: 'persisted tutorial' }]],
        ['tools', [{ id: 'iteration', name: 'persisted tool', description: 'persisted description' }]],
      ] as const) {
        const response = await fetch(`${contentUrl}/__orchard_playtest/content/${document}`, {
          method: 'POST',
          headers: { 'content-type': 'application/json' },
          body: JSON.stringify({ content }),
        })
        expect(response.ok).toBe(true)
        await new Promise((resolveDelay) => setTimeout(resolveDelay, 750))
        expect(await page.locator('body').getAttribute('data-visits')).toBe('1')
      }
      expect(await page.locator('body').getAttribute('data-tutorial')).toContain('initial tutorial')
      expect(await page.locator('body').getAttribute('data-tools')).toContain('initial tool')

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
