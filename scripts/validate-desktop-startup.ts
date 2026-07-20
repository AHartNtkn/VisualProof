import { strict as assert } from 'node:assert'
import { spawn } from 'node:child_process'
import { cp, mkdtemp, mkdir, readFile, readdir, rm, writeFile } from 'node:fs/promises'
import { createRequire } from 'node:module'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { _electron } from '@playwright/test'

const projectRoot = process.cwd()
const scratch = await mkdtemp(path.join(tmpdir(), 'cursebreaker-desktop-startup-'))
const electronPath = createRequire(import.meta.url)('electron') as string

const isolatedEnvironment = (configurationRoot: string): Record<string, string> => {
  const environment = Object.fromEntries(
    Object.entries(process.env).filter((entry): entry is [string, string] =>
      typeof entry[1] === 'string'),
  )
  environment.XDG_CONFIG_HOME = configurationRoot
  environment.XDG_SESSION_TYPE = 'x11'
  delete environment.WAYLAND_DISPLAY
  return environment
}

const obsoleteSave = {
  format: 'cursebreaker-save',
  version: 3,
  acknowledgedTeachers: ['obsolete-teacher-state'],
  settings: { reducedMotion: false, fullscreen: false, textSize: 'medium' },
}

const runFatalFixture = async (): Promise<{ code: number | null; stderr: string }> => {
  const applicationRoot = path.join(scratch, 'fatal-application')
  await mkdir(applicationRoot, { recursive: true })
  await cp(path.join(projectRoot, 'dist-electron'), path.join(applicationRoot, 'dist-electron'), {
    recursive: true,
  })
  await writeFile(path.join(applicationRoot, 'package.json'), JSON.stringify({
    name: 'cursebreaker-fatal-startup-fixture',
    type: 'module',
    main: 'dist-electron/main.js',
  }), 'utf8')
  const configurationRoot = path.join(scratch, 'fatal-config')
  await mkdir(configurationRoot, { recursive: true })

  return new Promise((resolve, reject) => {
    const child = spawn(electronPath, ['--ozone-platform=x11', applicationRoot], {
      env: isolatedEnvironment(configurationRoot),
      stdio: ['ignore', 'ignore', 'pipe'],
    })
    let stderr = ''
    child.stderr.setEncoding('utf8')
    child.stderr.on('data', (chunk: string) => { stderr += chunk })
    const deadline = setTimeout(() => {
      child.kill('SIGKILL')
      reject(new Error('fatal startup fixture did not exit before its deadline'))
    }, 10_000)
    child.once('error', reject)
    child.once('exit', (code) => {
      clearTimeout(deadline)
      resolve({ code, stderr })
    })
  })
}

try {
  const configurationRoot = path.join(scratch, 'recovery-config')
  const saveDirectory = path.join(
    configurationRoot,
    'visual-proof-assistant',
    'cursebreaker-save',
  )
  await mkdir(saveDirectory, { recursive: true })
  await writeFile(path.join(saveDirectory, 'save.json'), JSON.stringify(obsoleteSave), 'utf8')

  const application = await _electron.launch({
    args: ['--ozone-platform=x11', projectRoot],
    env: isolatedEnvironment(configurationRoot),
    timeout: 15_000,
  })
  try {
    const window = await application.firstWindow({ timeout: 15_000 })
    await window.locator('.curse-production-environment[data-mode="archive"]')
      .waitFor({ state: 'visible', timeout: 15_000 })
    await window.locator('.curse-folio-record[data-status="unlocked"]')
      .first()
      .waitFor({ state: 'visible', timeout: 15_000 })

    const replacement = JSON.parse(await readFile(path.join(saveDirectory, 'save.json'), 'utf8'))
    assert.equal(replacement.format, 'cursebreaker-save')
    assert.equal(replacement.version, 5)
    assert.equal(replacement.mode, 'archive')
    const files = await readdir(saveDirectory)
    const rejectedName = files.find((name) => /^rejected-save-[\da-f-]+\.json$/.test(name))
    assert.ok(rejectedName, 'rejected save was not retained')
    const rejected = JSON.parse(await readFile(path.join(saveDirectory, rejectedName), 'utf8'))
    assert.deepEqual(rejected, obsoleteSave)
    assert.equal(await window.locator('.curse-launch-failure').count(), 0)
  } finally {
    await application.close()
  }

  const fatal = await runFatalFixture()
  assert.equal(fatal.code, 1)
  assert.match(fatal.stderr, /Failed to start Cursebreaker/)
  assert.doesNotMatch(fatal.stderr, /Close this window and try again/)
  console.log('desktop startup recovery and fatal-exit validation passed')
} finally {
  await rm(scratch, { recursive: true, force: true })
}
