import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { propWalkFamily } from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { containsDoubleNegation, usedAtoms } from '../../src/generate/prop/formula'
import { formulaToDiagram } from '../../src/formula'
import { isAncestorOrEqual, sameDiagram } from '../../src/kernel/diagram'
import { childCuts, nodesIn } from '../../src/generate/diagram-scan'
import type { Diagram, RegionId } from '../../src/kernel/diagram/diagram'

/** The body region, identified the same way readPropTheorem does: the
 *  root's single cut, then that cut's single child cut. */
function findBodyRegion(diagram: Diagram): RegionId {
  const outer = childCuts(diagram, diagram.root)[0]!
  return childCuts(diagram, outer)[0]!
}

/** True iff some cut region strictly inside `body` is an empty-annulus
 *  double-cut pair (exactly one child cut, no nodes) — the shape
 *  doubleCutElim removes. */
function hasEmptyDoubleCutBelow(diagram: Diagram, body: RegionId): boolean {
  return Object.entries(diagram.regions).some(([id, region]) => {
    if (region.kind !== 'cut') return false
    if (id === body) return false
    if (!isAncestorOrEqual(diagram, body, id)) return false
    return childCuts(diagram, id).length === 1 && nodesIn(diagram, id).length === 0
  })
}

describe('propWalkFamily', () => {
  it('is registered second', () => {
    expect(GENERATOR_FAMILIES.map(({ id }) => id)).toEqual(['prop-shrink', 'prop-walk'])
  })
  it('generates certified, minimal, readable theorems (seed batch)', () => {
    // Measured (¬¬-repair wave): with the 'atoms' knob as an upper bound
    // (unused declared propositions are cleaned up, not rejected — see
    // family.ts) and doubled negation now REPAIRED by normalization
    // (recorded doubleCutElim steps) rather than rejected, seeds 1/2/3 at
    // length 6 first succeed at attempt 1/10/48 respectively — far fewer
    // than the pre-repair 54/205/539, since the ¬¬-rejection source of
    // failed candidates is gone (a walk is now rejected for containing ¬¬
    // only in the rare case a pin sits inside the pair's annulus). A wider
    // sweep over seeds 1-10 puts the worst case at attempt 48 (seed 3);
    // attempts:100 gives ~2x headroom over that worst case.
    for (const seed of [1, 2, 3]) {
      const problem = propWalkFamily.generate(
        { atoms: 2, length: 6, attempts: 100 },
        seededRng(seed),
      )
      // checkTheorem already ran inside generate (it throws on a bad
      // derivation); re-verify the outward contract here:
      const reading = readPropTheorem(problem.diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      expect(isMinimalTautology(reading.formula, reading.wires.length)).toBe(true)
      expect(containsDoubleNegation(reading.formula)).toBe(false)
      expect(hasEmptyDoubleCutBelow(problem.diagram, findBodyRegion(problem.diagram))).toBe(false)
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
