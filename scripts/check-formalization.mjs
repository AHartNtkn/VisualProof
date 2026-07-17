import { readdirSync, readFileSync, statSync } from 'node:fs'
import { join } from 'node:path'
import { spawnSync } from 'node:child_process'

function fail(message) {
  process.stderr.write(`${message}\n`)
  process.exit(1)
}

function run(command, args) {
  process.stdout.write(`> ${command} ${args.join(' ')}\n`)
  const result = spawnSync(command, args, {
    cwd: process.cwd(),
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
  })
  if (result.status !== 0) {
    fail(`${command} ${args.join(' ')} failed\n${result.stdout}${result.stderr}`)
  }
  if (result.stdout) process.stdout.write(result.stdout)
  if (result.stderr) process.stderr.write(result.stderr)
}

function leanFiles(root) {
  const files = []
  for (const entry of readdirSync(root)) {
    const path = join(root, entry)
    if (statSync(path).isDirectory()) files.push(...leanFiles(path))
    else if (path.endsWith('.lean')) files.push(path)
  }
  return files
}

function scanLeanSources() {
  const failures = []
  for (const path of leanFiles('VisualProof')) {
    const lines = readFileSync(path, 'utf8').split(/\r?\n/)
    lines.forEach((line, index) => {
      if (/^\s*axiom\b/.test(line)) {
        failures.push(`${path}:${index + 1}: project axiom declaration`)
      }
    })
  }
  if (failures.length) fail(failures.join('\n'))
  process.stdout.write('Lean source scan found no project axioms.\n')
}

run('node', ['scripts/check-source-size.mjs'])
run('lake', ['build'])
scanLeanSources()
run('lake', ['env', 'lean', 'VisualProof/Audit.lean'])
run('npm', ['run', 'formal:tags'])
run('npx', ['vitest', 'run', '--config', 'vitest.config.ts',
  'tests/kernel/formal/correspondence.test.ts'])
run('npm', ['run', 'typecheck'])
