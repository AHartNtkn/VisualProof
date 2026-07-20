import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

const sourceFiles = (directory: string): string[] => readdirSync(directory, { withFileTypes: true })
  .flatMap((entry) => {
    const path = join(directory, entry.name)
    return entry.isDirectory() ? sourceFiles(path) : [path]
  })
  .filter((path) => /\.(?:ts|tsx)$/.test(path))

describe('ordinary theorem and authored teaching source authority', () => {
  it('contains no displaced artifact-step or generic teacher authority', () => {
    const contents = sourceFiles('src/game')
      .map((path) => `${path}\n${readFileSync(path, 'utf8')}`)
      .join('\n')
    const forbidden = [
      ['Vellum', 'Step'].join(''),
      ['vel', 'lumManifest'].join(''),
      ['vel', 'lumDissolve'].join(''),
      ['grants', 'Vellum'].join(''),
      ['canUse', 'Vellum'].join(''),
      ['game/vel', 'lum'].join(''),
      ['./vel', 'lum'].join(''),
      ['kind: ', "'st", "alled'"].join(''),
      ['kind: ', "'proof", "State'"].join(''),
    ]

    for (const token of forbidden) expect(contents).not.toContain(token)
  })

  it('defines no timed or generic hint signal in teaching', () => {
    const teaching = readFileSync('src/game/teaching.ts', 'utf8').toLowerCase()
    expect(teaching).not.toContain(['ti', 'mer'].join(''))
    expect(teaching).not.toContain(['hi', 'nt'].join(''))
  })
})
