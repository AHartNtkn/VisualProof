import { copyFileSync, existsSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'
import type { TauriCapabilities, TauriServiceOptions } from '@wdio/tauri-service'

const repositoryRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..')
const application = process.env['GAME_E2E_APPLICATION']
  ?? resolve(repositoryRoot, 'src-tauri/target/debug/orchard-game')
const appIdentifier = 'com.visualproofassistant.orchard'
const logDirectory = join(tmpdir(), 'orchard-game-native-logs')
mkdirSync(logDirectory, { recursive: true })

type NativeScenario = {
  readonly name: string
  readonly spec: string
  readonly port: number
  readonly save?: string
  readonly invalidSave?: boolean
}

const scenarios: Readonly<Record<string, NativeScenario>> = {
  controls: { name: 'controls', spec: './e2e/controls.e2e.ts', port: 4545, save: 'large-1.sqlite3', invalidSave: true },
  'order-loop': { name: 'order-loop', spec: './e2e/order-loop.e2e.ts', port: 4550 },
  'sprout-spawn': { name: 'sprout-spawn', spec: './e2e/sprout-spawn.e2e.ts', port: 4551 },
  ...Object.fromEntries([10, 50, 100, 250, 500, 1000, 2000].map((count, index) => [
    `stress-${count}`,
    { name: `stress-${count}`, spec: './e2e/stress.e2e.ts', port: 4600 + index, save: `stress-${count}.sqlite3` },
  ])),
}

const requestedScenario = process.env['GAME_E2E_SCENARIO'] ?? 'controls'
const scenario = scenarios[requestedScenario]
if (scenario === undefined) throw new Error(`unknown native game scenario '${requestedScenario}'`)

const suppliedDataRoot = process.env['GAME_E2E_DATA_ROOT']
const appDataRoot = suppliedDataRoot ?? mkdtempSync(join(tmpdir(), `orchard-game-${scenario.name}-`))
const saveDirectory = join(appDataRoot, appIdentifier, 'saves')
if (scenario.save !== undefined || scenario.invalidSave === true) mkdirSync(saveDirectory, { recursive: true })
if (scenario.save !== undefined) {
  const destination = join(saveDirectory, scenario.save)
  if (!existsSync(destination)) {
    copyFileSync(resolve(repositoryRoot, 'game/generated-saves', scenario.save), destination)
  }
}
if (scenario.invalidSave === true) writeFileSync(join(saveDirectory, 'unreadable.sqlite3'), 'not a SQLite database')

const nativeEnvironment = {
  XDG_DATA_HOME: appDataRoot,
  DISPLAY: process.env['DISPLAY'] ?? '',
  GDK_BACKEND: 'x11',
}
if (nativeEnvironment.DISPLAY.length === 0) throw new Error('native game tests require a private X11 DISPLAY')

const serviceOptions: TauriServiceOptions = {
  driverProvider: 'embedded',
  embeddedPort: scenario.port,
  env: nativeEnvironment,
  captureBackendLogs: true,
  captureFrontendLogs: true,
  startTimeout: 60_000,
}

const capability: TauriCapabilities = {
  browserName: 'tauri',
  'tauri:options': { application },
  'wdio:specs': [scenario.spec],
  'wdio:tauriServiceOptions': serviceOptions,
}

export const config: WebdriverIO.Config = {
  runner: 'local',
  specs: [scenario.spec],
  maxInstances: 1,
  maxInstancesPerCapability: 1,
  capabilities: [capability],
  services: [['@wdio/tauri-service', { ...serviceOptions, appBinaryPath: application }]],
  outputDir: logDirectory,
  logLevel: process.env['GAME_E2E_DEBUG'] === '1' ? 'debug' : 'error',
  bail: 0,
  waitforTimeout: 30_000,
  connectionRetryTimeout: 90_000,
  connectionRetryCount: 1,
  framework: 'mocha',
  reporters: ['spec'],
  mochaOpts: { ui: 'bdd', timeout: 12 * 60_000 },
  ...(suppliedDataRoot === undefined
    ? { onComplete: () => rmSync(appDataRoot, { recursive: true, force: true }) }
    : {}),
}
