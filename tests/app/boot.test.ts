import { describe, it, expect } from 'vitest'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mergeTheories } from '../../src/app/boot'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'

describe('mergeTheories (the only thing boot.ts does — no fetch, no manifest)', () => {
  it('merges a bundle: theorems citable, relation present', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    const merged = mergeTheories([frege])
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
    expect(merged.relations['nat']).toBeDefined()
  })

  it('empty input rebuilds to the empty context (the honest empty boot)', () => {
    const merged = mergeTheories([])
    expect(merged.ctx).toBe(EMPTY_PROOF_CONTEXT)
    expect([...merged.ctx.theorems.keys()]).toEqual([])
    expect(Object.keys(merged.relations)).toEqual([])
  })

  it('refuses conflicting theorem names loudly', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    expect(() => mergeTheories([frege, frege]))
      .toThrowError(/theory merge conflict: duplicate theorem 'plusAssoc'/)
  })

  it('rebuilds from the certified snapshot rather than a mutated parsed theory', () => {
    const loaded = loadTheory(theoryToJson(buildFregeTheory()))
    delete (loaded.theory.relations as Record<string, unknown>).nat
    ;(loaded.theory.theorems as unknown[]).splice(0)
    const merged = mergeTheories([loaded])
    expect(merged.ctx.relations.has('nat')).toBe(true)
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
  })
})
