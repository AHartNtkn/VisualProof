import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { propWalkFamily } from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { containsDoubleNegation, usedAtoms } from '../../src/generate/prop/formula'
import { formulaToDiagram } from '../../src/formula'
import { sameDiagram } from '../../src/kernel/diagram'

describe('propWalkFamily', () => {
  it('is registered second', () => {
    expect(GENERATOR_FAMILIES.map(({ id }) => id)).toEqual(['prop-shrink', 'prop-walk'])
  })
  it('generates certified, minimal, readable theorems (seed batch)', () => {
    // Measured: with the 'atoms' knob as an upper bound (unused declared
    // propositions are cleaned up, not rejected — see family.ts) and the
    // doubled-negation filter now also rejecting candidates, seeds 1/2/3 at
    // length 6 first succeed at attempt 54/205/539 respectively (seed 3
    // moved from 338 before the filter to 539 after it); attempts:900 gives
    // ~1.7x headroom over the worst case. That headroom costs ~4.3s combined
    // wall time (measured across repeated runs), too close to the default
    // 5s test timeout, so this test gets the same explicit 10s timeout
    // generate-entry.test.ts already uses for its generate-heavy case.
    for (const seed of [1, 2, 3]) {
      const problem = propWalkFamily.generate(
        { atoms: 2, length: 6, attempts: 900 },
        seededRng(seed),
      )
      // checkTheorem already ran inside generate (it throws on a bad
      // derivation); re-verify the outward contract here:
      const reading = readPropTheorem(problem.diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      expect(isMinimalTautology(reading.formula, reading.wires.length)).toBe(true)
      expect(containsDoubleNegation(reading.formula)).toBe(false)
      expect(sameDiagram(formulaToDiagram(problem.statement), problem.diagram)).toBe(true)
      expect(problem.walkUpperBound).toBeGreaterThan(0)
    }
  }, 10_000)
  it('throws loudly when the attempt cap is exhausted', () => {
    // attempts=1 with a long walk over 1 atom essentially never survives the
    // minimality filter on the first try for this seed; assert the loud error.
    expect(() => propWalkFamily.generate({ atoms: 1, length: 12, attempts: 1 }, seededRng(4)))
      .toThrow(/attempts/)
  })
})
