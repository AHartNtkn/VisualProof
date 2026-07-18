import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { describe, expect, it } from 'vitest'

const source = (name: string): string => readFileSync(resolve(`src/game/interface/${name}`), 'utf8')

describe('game-owned proof surface boundaries', () => {
  it('has no assistant, review-demo, storage, Electron, or obsolete asset imports', () => {
    const combined = [
      'artifact-drop.ts',
      'proof-motion.ts',
      'proof-moves.ts',
      'proof-surface.ts',
      'timeline-lever.ts',
    ].map(source).join('\n')
    expect(combined).not.toMatch(/(?:\.\.\/)+app(?:\/|')|review\/|localStorage|electron/i)
    expect(combined).not.toMatch(/lever-(?:housing|handle)\.png|shadow\.png|glass\.png|frame\.png/)
  })

  it('renders the proof canvas transparently and contains no generic theorem UI path', () => {
    const combined = `${source('proof-surface.ts')}\n${source('proof-moves.ts')}`
    expect(combined).toMatch(/clearRect/)
    expect(combined).toMatch(/construction\.hostClaim/)
    expect(combined).toMatch(/physicsEnabled:[^\n]*construction === null/)
    expect(combined).toMatch(/zoomEnabled:[^\n]*construction === null/)
    expect(combined).not.toMatch(/fillRect\s*\(/)
    expect(combined).not.toMatch(/Applicable theorems|Closed theorems|citation cycle|armed reference|citeTheorem/i)
  })

  it('leaves the gasket as the sole outer boundary while retaining canvas focus', () => {
    const css = source('proof-surface.css')
    expect(css).toMatch(/curse-game-proof-canvas[^}]*border:\s*0[^}]*outline:\s*0/s)
    expect(source('proof-surface.ts')).toMatch(
      /paint\([^\n]+\)\.filter\(\(shape\) => shape\.kind !== 'frame'\)/,
    )
  })
})
