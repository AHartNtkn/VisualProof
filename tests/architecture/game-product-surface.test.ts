import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

describe('game branch browser product', () => {
  it('mounts Cursebreaker without an assistant product entry', () => {
    const main = readFileSync('app/main.ts', 'utf8')
    const html = readFileSync('app/index.html', 'utf8')
    expect(main).toContain('mountCursebreaker')
    expect(main).not.toContain('mountShell')
    expect(html).toContain('<main id="cursebreaker"></main>')
    expect(html).not.toContain('id="chrome"')
    expect(html).not.toContain('Visual Proof Assistant')
  })
})
