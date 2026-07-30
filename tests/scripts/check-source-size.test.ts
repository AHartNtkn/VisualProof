import { copyFileSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { spawnSync } from 'node:child_process'
import { afterEach, describe, expect, test } from 'vitest'

const temporaryRoots: string[] = []

function fixtureRoot(): string {
  const root = mkdtempSync(join(tmpdir(), 'visualproof-size-audit-'))
  temporaryRoots.push(root)
  mkdirSync(join(root, 'scripts'))
  copyFileSync(
    join(process.cwd(), 'scripts', 'check-source-size.mjs'),
    join(root, 'scripts', 'check-source-size.mjs'),
  )
  return root
}

function runAudit(root: string) {
  return spawnSync('node', ['scripts/check-source-size.mjs'], {
    cwd: root,
    encoding: 'utf8',
  })
}

afterEach(() => {
  for (const root of temporaryRoots.splice(0)) {
    rmSync(root, { recursive: true, force: true })
  }
})

describe('source-size audit', () => {
  test('rejects an oversized maintained source file', () => {
    const root = fixtureRoot()
    mkdirSync(join(root, 'src'), { recursive: true })
    writeFileSync(
      join(root, 'src', 'oversized.ts'),
      `${'line\n'.repeat(3001)}`,
    )

    const result = runAudit(root)

    expect(result.status).toBe(1)
    expect(result.stderr).toContain('3001 src/oversized.ts')
  })

  test('excludes external dependencies, build outputs, and workflow artifacts', () => {
    const root = fixtureRoot()
    for (const directory of [
      '.lake',
      '.superpowers',
      'archive',
      'build',
      'coverage',
      'dist',
      'examples',
      'node_modules',
      'scratchpad',
    ]) {
      mkdirSync(join(root, directory), { recursive: true })
      writeFileSync(
        join(root, directory, 'oversized.txt'),
        `${'line\n'.repeat(3001)}`,
      )
    }

    const result = runAudit(root)

    expect(result.status).toBe(0)
    expect(result.stdout).toContain(
      'no maintained text file exceeds 3000 lines',
    )
  })
})
