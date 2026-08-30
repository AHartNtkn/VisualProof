import { chromium, type Browser } from '@playwright/test'
import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process'
import {
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs'
import { createServer as createTcpServer } from 'node:net'
import { tmpdir } from 'node:os'
import { join, resolve } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'

const repositoryRoot = resolve(import.meta.dirname, '../..')

let browser: Browser | undefined
let viteProcess: ChildProcessWithoutNullStreams | undefined
let viteOutput = ''
let fixtureRoot: string | undefined
let contentProcess: ChildProcessWithoutNullStreams | undefined
let contentOutput = ''
let contentStopPath: string | undefined

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

async function startContentServer(origin: string): Promise<string> {
  if (fixtureRoot === undefined) throw new Error('Vite watch fixture is not initialized')
  const port = await reserveAvailablePort()
  contentStopPath = join(fixtureRoot, 'content-server.stop')
  contentProcess = spawn('cargo', [
    'test',
    '--manifest-path',
    join(repositoryRoot, 'src-tauri/Cargo.toml'),
    '--all-features',
    'playtest_server::tests::vite_authored_content_server',
    '--',
    '--ignored',
    '--nocapture',
  ], {
    cwd: repositoryRoot,
    env: {
      ...process.env,
      ORCHARD_TEST_CONTENT_PORT: String(port),
      ORCHARD_TEST_CONTENT_ORIGIN: origin,
      ORCHARD_TEST_CONTENT_ROOT: join(fixtureRoot, 'game/content'),
      ORCHARD_TEST_CONTENT_STOP: contentStopPath,
    },
  })
  contentProcess.stdout.on('data', (chunk: Buffer) => {
    contentOutput += chunk.toString()
  })
  contentProcess.stderr.on('data', (chunk: Buffer) => {
    contentOutput += chunk.toString()
  })
  const baseUrl = `http://127.0.0.1:${port}`
  const deadline = Date.now() + 30_000
  while (Date.now() < deadline) {
    if (contentProcess.exitCode !== null) {
      throw new Error(`Playtest content server exited before becoming ready:\n${contentOutput}`)
    }
    try {
      const response = await fetch(`${baseUrl}/__orchard_playtest/health`, {
        headers: {
          origin,
          'x-orchard-playtest-token': 'orchard-playtest-token',
        },
      })
      if (response.status === 204) return baseUrl
    } catch {
      // Cargo or the test server is still starting.
    }
    await new Promise((resolveDelay) => setTimeout(resolveDelay, 50))
  }
  throw new Error(`Playtest content server did not become ready:\n${contentOutput}`)
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

async function stopContentServer(): Promise<void> {
  const runningProcess = contentProcess
  contentProcess = undefined
  if (runningProcess === undefined || runningProcess.exitCode !== null) return
  if (contentStopPath !== undefined) writeFileSync(contentStopPath, 'stop\n')
  const exited = new Promise<void>((resolveExit) => {
    runningProcess.once('exit', () => resolveExit())
  })
  await Promise.race([
    exited,
    new Promise<void>((resolveTimeout) => setTimeout(resolveTimeout, 5_000)),
  ])
  if (runningProcess.exitCode === null) {
    runningProcess.kill('SIGTERM')
    await exited
  }
}

afterEach(async () => {
  await browser?.close()
  browser = undefined

  await stopVite()
  viteOutput = ''

  await stopContentServer()
  contentOutput = ''
  contentStopPath = undefined

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
      copyFileSync(
        join(repositoryRoot, 'game/content/tutorial.json'),
        join(fixtureRoot, 'game/content/tutorial.json'),
      )
      copyFileSync(
        join(repositoryRoot, 'game/content/tools.json'),
        join(fixtureRoot, 'game/content/tools.json'),
      )
      writeEntry('initial')

      const gameConfig = join(repositoryRoot, 'game/vite.config.ts')
      if (existsSync(gameConfig)) {
        copyFileSync(gameConfig, join(fixtureRoot, 'game/vite.config.ts'))
      }

      const port = await reserveAvailablePort()
      const url = `http://127.0.0.1:${port}`
      const contentUrl = await startContentServer(url)
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

      const tutorial = JSON.parse(readFileSync(
        join(fixtureRoot, 'game/content/tutorial.json'),
        'utf8',
      )) as Array<{ milestoneId: string; text: string }>
      const tools = JSON.parse(readFileSync(
        join(fixtureRoot, 'game/content/tools.json'),
        'utf8',
      )) as Array<{ id: string; name: string; description: string }>
      const initialTutorial = tutorial[0]!.text
      const initialTool = tools[0]!.name
      const persistedTutorial = tutorial.map((record, index) => index === 0
        ? { ...record, text: 'persisted tutorial' }
        : record)
      const persistedTools = tools.map((record, index) => index === 0
        ? { ...record, name: 'persisted tool' }
        : record)
      const headers = {
        'content-type': 'application/json',
        origin: url,
        'x-orchard-playtest-token': 'orchard-playtest-token',
      }

      const saveShaped = await fetch(`${contentUrl}/__orchard_playtest/content/tutorial`, {
        method: 'POST',
        headers,
        body: JSON.stringify({ slotId: 'must-not-be-accepted', content: persistedTutorial }),
      })
      expect(saveShaped.status).toBe(422)

      for (const [document, content] of [
        ['tutorial', persistedTutorial],
        ['tools', persistedTools],
      ] as const) {
        const response = await fetch(`${contentUrl}/__orchard_playtest/content/${document}`, {
          method: 'POST',
          headers,
          body: JSON.stringify({ content }),
        })
        expect(response.ok).toBe(true)
        await new Promise((resolveDelay) => setTimeout(resolveDelay, 750))
        expect(await page.locator('body').getAttribute('data-visits')).toBe('1')
      }
      expect(readFileSync(join(fixtureRoot, 'game/content/tutorial.json'), 'utf8'))
        .toContain('persisted tutorial')
      expect(readFileSync(join(fixtureRoot, 'game/content/tools.json'), 'utf8'))
        .toContain('persisted tool')
      expect(await page.locator('body').getAttribute('data-tutorial')).toContain(initialTutorial)
      expect(await page.locator('body').getAttribute('data-tools')).toContain(initialTool)

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
    45_000,
  )
})
