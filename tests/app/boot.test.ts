import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory, loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mergeTheories } from '../../src/app/boot'

const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

describe('mergeTheories (the only thing boot.ts does — no fetch, no manifest)', () => {
  it('merges a bundle: theorems citable, relation present, no constants (const-free theory)', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    const merged = mergeTheories([frege])
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
    // the relational frege theory carries no term constants
    expect(merged.constNames.size).toBe(0)
    expect(merged.relations['nat']).toBeDefined()
  })

  it('empty input rebuilds to the empty context (the honest empty boot)', () => {
    const merged = mergeTheories([])
    expect([...merged.ctx.theorems.keys()]).toEqual([])
    expect(merged.constNames.size).toBe(0)
    expect(Object.keys(merged.relations)).toEqual([])
  })

  it('refuses conflicting definition bodies loudly', () => {
    const one = { definitions: { ONE: pp('\\f. \\x. x') }, relations: {}, theorems: [] }
    const other = { definitions: { ONE: pp('\\f. \\x. f x') }, relations: {}, theorems: [] }
    const a = { theory: one, ctx: verifyTheory(one) }
    const b = { theory: other, ctx: verifyTheory(other) }
    expect(() => mergeTheories([a, b]))
      .toThrowError(/theory merge conflict: definition 'ONE'/)
  })
})
