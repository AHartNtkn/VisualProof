import { describe, it, expect } from 'vitest'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mergeTheories } from '../../src/app/boot'

describe('mergeTheories (the only thing boot.ts does — no fetch, no manifest)', () => {
  it('merges a bundle: theorems citable, relation present', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    const merged = mergeTheories([frege])
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
    expect(merged.relations['nat']).toBeDefined()
  })

  it('empty input rebuilds to the empty context (the honest empty boot)', () => {
    const merged = mergeTheories([])
    expect([...merged.ctx.theorems.keys()]).toEqual([])
    expect(Object.keys(merged.relations)).toEqual([])
  })

  it('refuses conflicting theorem names loudly', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    expect(() => mergeTheories([frege, frege]))
      .toThrowError(/theory merge conflict: duplicate theorem 'plusAssoc'/)
  })
})
