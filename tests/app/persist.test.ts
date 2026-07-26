import { describe, expect, it } from 'vitest'
import { sessionTheory } from '../../src/app/persist'
import { verifyTheory } from '../../src/kernel/proof/context'
import { loadTheory, theoryToJson } from '../../src/kernel/proof/store'
import { tinyTheory } from '../fixtures/zero-signature'

describe('session persistence', () => {
  it('round-trips structural relations and theorems without theory-specific fields', () => {
    const theory = tinyTheory()
    const ctx = verifyTheory(theory)
    const saved = sessionTheory(ctx, { relations: [...ctx.relations] })
    const loaded = loadTheory(theoryToJson(saved))
    expect([...loaded.ctx.relations.keys()]).toEqual(['UnaryWitness'])
    expect([...loaded.ctx.theorems.keys()]).toEqual(['StructuralReflexivity'])
  })
})
