import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { verifyTheory, loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { bootBundledContext, mergeTheories } from '../../src/app/boot'

const noConsts = new Set<string>()
const pp = (s: string) => parseTerm(s, noConsts)

describe('bundled boot context', () => {
  it('merges both bundled theories: all five theorems citable, constants unioned', () => {
    const boot = bootBundledContext()
    expect([...boot.ctx.theorems.keys()].sort()).toEqual(
      ['fixedPoint', 'onePlusOne', 'oneIsNat', 'succNat', 'zeroIsNat'].sort(),
    )
    for (const name of ['ZERO', 'SUCC', 'PLUS', 'ONE', 'TWO', 'Y']) {
      expect(boot.constNames.has(name)).toBe(true)
    }
    expect(boot.relations['nat']).toBeDefined()
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
