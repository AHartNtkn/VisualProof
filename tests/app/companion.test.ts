import { describe, expect, it } from 'vitest'
import { companionFor } from '../../src/app/companion'
import { mkReplay } from '../../src/app/replay'
import { verifyTheory } from '../../src/kernel/proof/context'
import { tinyTheory } from '../fixtures/zero-signature'

describe('companion projection', () => {
  it('shows only an active replay goal', () => {
    const ctx = verifyTheory(tinyTheory())
    const replay = mkReplay('StructuralReflexivity', ctx)
    expect(companionFor({ mode: 'edit', replay })).toBeNull()
    expect(companionFor({ mode: 'prove', replay })).toBeNull()
    expect(companionFor({ mode: 'replay', replay: null })).toBeNull()
    expect(companionFor({ mode: 'replay', replay })?.label).toBe('goal: final state')
  })
})
