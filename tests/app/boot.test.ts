import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory, loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { mergeTheories } from '../../src/app/boot'

const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

describe('mergeTheories (the only thing boot.ts does — no fetch, no manifest)', () => {
  it('merges a bundle: theorems citable, constants unioned, relation present', () => {
    const frege = loadTheory(theoryToJson(buildFregeTheory()))
    const merged = mergeTheories([frege])
    expect(merged.ctx.theorems.has('plusAssoc')).toBe(true)
    for (const name of ['ZERO', 'SUCC', 'PLUS', 'ONE']) {
      expect(merged.constNames.has(name)).toBe(true)
    }
    expect(merged.relations['nat']).toBeDefined()
  })

  it('empty input rebuilds to the empty context (the honest empty boot)', () => {
    const merged = mergeTheories([])
    expect([...merged.ctx.theorems.keys()]).toEqual([])
    expect(merged.constNames.size).toBe(0)
    expect(Object.keys(merged.relations)).toEqual([])
  })

  it('refuses conflicting definition bodies loudly', () => {
    const frege = buildFregeTheory()
    const loaded = loadTheory(JSON.parse(JSON.stringify(theoryToJson(frege))))
    const conflicting = {
      theory: { definitions: { ONE: pp('\\f. \\x. x') }, relations: {}, theorems: [] },
      ctx: verifyTheory({ definitions: { ONE: pp('\\f. \\x. x') }, relations: {}, theorems: [] }),
    }
    expect(() => mergeTheories([loaded, conflicting]))
      .toThrowError(/theory merge conflict: definition 'ONE'/)
  })
})
