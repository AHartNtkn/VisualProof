import { describe, expect, it } from 'vitest'
import { mergeTheories } from '../../src/app/boot'
import { verifyTheory } from '../../src/kernel/proof/context'
import { tinyTheory } from '../fixtures/zero-signature'

describe('theory boot merge', () => {
  it('merges a verified zero-signature theory', () => {
    const theory = tinyTheory()
    const merged = mergeTheories([{ theory, ctx: verifyTheory(theory) }])
    expect([...merged.ctx.relations.keys()]).toEqual(['UnaryWitness'])
    expect([...merged.ctx.theorems.keys()]).toEqual(['StructuralReflexivity'])
  })

  it('refuses duplicate names instead of shadowing', () => {
    const theory = tinyTheory()
    const loaded = { theory, ctx: verifyTheory(theory) }
    expect(() => mergeTheories([loaded, loaded])).toThrow(/duplicate theorem|duplicate relation/)
  })
})
