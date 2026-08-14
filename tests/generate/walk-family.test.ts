import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { propWalkFamily } from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { usedAtoms } from '../../src/generate/prop/formula'
import { formulaToDiagram } from '../../src/formula'
import { sameDiagram } from '../../src/kernel/diagram'

describe('propWalkFamily', () => {
  it('is registered second', () => {
    expect(GENERATOR_FAMILIES.map(({ id }) => id)).toEqual(['prop-shrink', 'prop-walk'])
  })
  it('generates certified, minimal, readable theorems (seed batch)', () => {
    // Measured: with the 'atoms' knob as an upper bound (unused declared
    // propositions are cleaned up, not rejected — see family.ts), seeds
    // 1/2/3 at length 6 first succeed at attempt 54/205/338 respectively
    // (~3.6s combined wall time here); attempts:500 gives ~1.5x headroom
    // over the worst case while staying well inside the 5s test timeout.
    for (const seed of [1, 2, 3]) {
      const problem = propWalkFamily.generate(
        { atoms: 2, length: 6, attempts: 500 },
        seededRng(seed),
      )
      // checkTheorem already ran inside generate (it throws on a bad
      // derivation); re-verify the outward contract here:
      const reading = readPropTheorem(problem.diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      expect(isMinimalTautology(reading.formula, reading.wires.length)).toBe(true)
      expect(sameDiagram(formulaToDiagram(problem.statement), problem.diagram)).toBe(true)
      expect(problem.walkUpperBound).toBeGreaterThan(0)
    }
  })
  it('throws loudly when the attempt cap is exhausted', () => {
    // attempts=1 with a long walk over 1 atom essentially never survives the
    // minimality filter on the first try for this seed; assert the loud error.
    expect(() => propWalkFamily.generate({ atoms: 1, length: 12, attempts: 1 }, seededRng(4)))
      .toThrow(/attempts/)
  })
})
