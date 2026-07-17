import { describe, it, expect } from 'vitest'
import { mkdtempSync, writeFileSync, readFileSync, existsSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { emitTheories } from '../../scripts/emit-theories'
import { loadTheory } from '../../src/kernel/proof/store'

describe('emitTheories (real filesystem)', () => {
  it('writes the example theory files as ordinary JSON — no manifest, verifiable by loadTheory', () => {
    const dir = mkdtempSync(join(tmpdir(), 'vpa-emit-'))
    try {
      const { written } = emitTheories(dir)
      expect(written).toEqual(['frege.json', 'lambda.json'])
      // no manifest/index is produced — the app never references these files
      expect(existsSync(join(dir, 'index.json'))).toBe(false)
      // the shipped files exist and load through the real verifying road
      for (const f of written) {
        expect(existsSync(join(dir, f))).toBe(true)
        const text = readFileSync(join(dir, f), 'utf8')
        expect(text.trimEnd().split('\n').length).toBeLessThanOrEqual(3000)
        expect(() => loadTheory(JSON.parse(text))).not.toThrow()
      }
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it('does not touch a user file already in the directory', () => {
    const dir = mkdtempSync(join(tmpdir(), 'vpa-emit-'))
    try {
      const mine = join(dir, 'mytheory.json')
      writeFileSync(mine, JSON.stringify({ custom: true }))
      emitTheories(dir)
      expect(JSON.parse(readFileSync(mine, 'utf8'))).toEqual({ custom: true })
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })
})
