import { describe, expect, it } from 'vitest'
import { readFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'

describe('game package boundary', () => {
  it('never imports proof-assistant product or bundled prototype theories', () => {
    const files = execFileSync('rg', ['--files', 'src/game'], { encoding: 'utf8' }).trim().split('\n')
    const offenders = files.filter((file) => {
      const source = readFileSync(file, 'utf8')
      return /from ['"]\.\.\/app\//.test(source)
        || /from ['"]\.\.\/theories\//.test(source)
        || /fsaccess/.test(source)
    })
    expect(offenders).toEqual([])
  })
})
