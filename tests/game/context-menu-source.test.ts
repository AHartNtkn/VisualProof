import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'

const source = (path: string): string => readFileSync(resolve(path), 'utf8')

describe('game context-menu style authority', () => {
  it('uses one semantic class family without private proof or inline construction palettes', () => {
    const proof = source('src/game/interface/proof-moves.ts')
    const spawn = source('src/game/interface/loupe/interact/spawn.ts')
    const proofCss = source('src/game/interface/proof-surface.css')

    expect(proof).toContain('curse-context-menu')
    expect(spawn).toContain('curse-context-menu')
    expect(proof).not.toMatch(/curse-proof-menu/)
    expect(proofCss).not.toMatch(/curse-proof-menu/)
    expect(spawn).not.toMatch(/#fff|#fef3c7|#d97706|#a8a29e|#78716c/)
    expect(spawn).not.toMatch(/style\.background\s*=/)
  })
})
