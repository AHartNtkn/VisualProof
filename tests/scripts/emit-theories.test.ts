import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories'

const FREGE_PATH = 'examples/frege.json'

function emitTheories(): void {
  execFileSync('npm', ['run', 'emit:theories'], {
    cwd: process.cwd(),
    stdio: 'pipe',
  })
}

describe('whole-theory emission', () => {
  it('emits one deterministic, ordinarily loadable Frege theory', () => {
    emitTheories()
    const first = readFileSync(FREGE_PATH)

    emitTheories()
    const second = readFileSync(FREGE_PATH)

    expect(second.equals(first)).toBe(true)
    expect(second.at(-1)).toBe(0x0a)
    expect(second.at(-2)).not.toBe(0x0a)
    const json = JSON.parse(second.toString('utf8')) as unknown
    const loaded = loadTheory(json)
    expect(theoryToJson(loaded.theory)).toEqual(theoryToJson(buildFregeTheory()))
    expect(loaded.ctx.theorems.has('existsProp')).toBe(true)
    expect(loaded.ctx.theorems.has('plusComm')).toBe(true)
  }, 120_000)
})
