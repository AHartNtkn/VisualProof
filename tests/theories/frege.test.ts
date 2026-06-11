import { describe, it, expect } from 'vitest'
import { buildFregeTheory } from '../../src/theories/frege'
import { verifyTheory, theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import { boundaryFingerprint } from '../../src/kernel/diagram/canonical/fingerprint'

describe('the bundled Frege theory', () => {
  it('verifies end to end: every theorem replays through its gates', () => {
    const theory = buildFregeTheory()
    const ctx = verifyTheory(theory)
    expect([...ctx.theorems.keys()]).toEqual(['zeroIsNat', 'succNat', 'oneIsNat'])
  })

  it('round-trips through the file format with re-verification', () => {
    const theory = buildFregeTheory()
    const text = JSON.stringify(theoryToJson(theory))
    const { ctx } = loadTheory(JSON.parse(text))
    expect(ctx.theorems.size).toBe(3)
  })

  it('oneIsNat is two theorem citations — compression, not expansion', () => {
    const theory = buildFregeTheory()
    const one = theory.theorems.find((t) => t.name === 'oneIsNat')!
    expect(one.steps).toHaveLength(2)
    expect(one.steps.every((s) => s.rule === 'theorem')).toBe(true)
  })

  it('the named ℕ relation is the shape the theorems use', () => {
    const theory = buildFregeTheory()
    expect(theory.relations['nat']).toBeDefined()
    expect(boundaryFingerprint(theory.relations['nat']!)).toBeTruthy()
    const succ = theory.theorems.find((t) => t.name === 'succNat')!
    expect(succ.lhs.boundary).toHaveLength(2)
    expect(succ.rhs.boundary).toHaveLength(2)
  })

  it('the theory is deterministic: two builds are identical', () => {
    const a = JSON.stringify(theoryToJson(buildFregeTheory()))
    const b = JSON.stringify(theoryToJson(buildFregeTheory()))
    expect(a).toBe(b)
  })
})
