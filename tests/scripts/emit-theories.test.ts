import { describe, it, expect } from 'vitest'
import { mkdtempSync, writeFileSync, readFileSync, existsSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { mergeManifest, emitTheories } from '../../scripts/emit-theories'

const noWarn = (): void => {}

describe('mergeManifest', () => {
  it('keeps foreign entries, shipped-first, deduped and ordered', () => {
    const shipped = ['frege.json', 'lambda.json']
    // existing manifest reorders shipped and interleaves two user entries
    const existing = JSON.stringify(['user-a.json', 'lambda.json', 'frege.json', 'user-b.json', 'user-a.json'])
    expect(mergeManifest(shipped, existing, noWarn)).toEqual([
      'frege.json',
      'lambda.json',
      'user-a.json',
      'user-b.json',
    ])
  })

  it('warns and rebuilds shipped-only when the manifest is missing', () => {
    const warnings: string[] = []
    expect(mergeManifest(['frege.json', 'lambda.json'], null, (m) => warnings.push(m))).toEqual([
      'frege.json',
      'lambda.json',
    ])
    expect(warnings.some((w) => /no existing manifest/i.test(w))).toBe(true)
  })

  it('warns and rebuilds shipped-only when the manifest is corrupt', () => {
    const warnings: string[] = []
    expect(mergeManifest(['frege.json', 'lambda.json'], 'not json{{', (m) => warnings.push(m))).toEqual([
      'frege.json',
      'lambda.json',
    ])
    expect(warnings.some((w) => /unparseable/i.test(w))).toBe(true)
  })

  it('warns when the manifest parses but is not an array of strings', () => {
    const warnings: string[] = []
    expect(mergeManifest(['frege.json'], JSON.stringify({ frege: 'frege.json' }), (m) => warnings.push(m))).toEqual([
      'frege.json',
    ])
    expect(warnings.some((w) => /not an array of file-name strings/i.test(w))).toBe(true)
  })
})

describe('emitTheories (real filesystem)', () => {
  it("re-emit preserves a user's custom theory file and its manifest entry, never deleting it", () => {
    const dir = mkdtempSync(join(tmpdir(), 'vpa-emit-'))
    try {
      // simulate the state after a user dropped a custom theory and listed it:
      // a prior emit manifest plus the user's file + entry
      writeFileSync(join(dir, 'index.json'), JSON.stringify(['frege.json', 'lambda.json', 'mytheory.json']))
      writeFileSync(join(dir, 'mytheory.json'), JSON.stringify({ custom: true }))

      const { manifest } = emitTheories(dir, noWarn)

      // shipped entries present and first
      expect(manifest.slice(0, 2)).toEqual(['frege.json', 'lambda.json'])
      // the user's entry survived the re-emit
      expect(manifest).toContain('mytheory.json')
      // the user's file was never touched or deleted
      expect(existsSync(join(dir, 'mytheory.json'))).toBe(true)
      expect(JSON.parse(readFileSync(join(dir, 'mytheory.json'), 'utf8'))).toEqual({ custom: true })
      // the on-disk manifest matches the returned one
      expect(JSON.parse(readFileSync(join(dir, 'index.json'), 'utf8'))).toEqual(manifest)
      // the shipped files were actually written
      expect(existsSync(join(dir, 'frege.json'))).toBe(true)
      expect(existsSync(join(dir, 'lambda.json'))).toBe(true)
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })
})
