import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { findDoubleCutToNormalize, findDuplicateToNormalize, propWalkFamily } from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { containsDoubleNegation, containsDuplicateConjunct, usedAtoms } from '../../src/generate/prop/formula'
import { deiterationStep } from '../../src/app/interact/moves'
import { formulaToDiagram } from '../../src/formula'
import { applyStep, EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof'
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
    // Measured (¬¬-repair wave, re-measured for the duplicate-repair wave):
    // with the 'atoms' knob as an upper bound (unused declared propositions
    // are cleaned up, not rejected — see family.ts) and both doubled
    // negation AND same-region duplicate conjuncts now REPAIRED by joint
    // normalization (recorded doubleCutElim/deiteration steps) rather than
    // rejected, seeds 1/2/3 at length 6 first succeed at attempt 2/11/49
    // respectively — re-measuring after adding the duplicate finder found
    // this within noise of the pre-duplicate-repair 1/10/48 (a walk is now
    // rejected for containing ¬¬ or a duplicate only in the rare case a pin
    // sits inside the removed content's scope). A wider sweep over seeds
    // 1-10 puts the worst case at attempt 49 (seed 3); attempts:100 gives
    // ~2x headroom over that worst case.
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
      expect(containsDuplicateConjunct(reading.formula)).toBe(false)
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

describe('findDoubleCutToNormalize', () => {
  it(
    'eliminates ¬¬¬(P ∧ ¬P) down to ¬(P ∧ ¬P) in exactly one doubleCutElim',
    () => {
      // ¬¬¬(P ∧ ¬P): the body holds three nested cuts before reaching the
      // and-content; the outermost two form a genuine empty-annulus
      // double-cut pair (each has exactly one child cut and no nodes of
      // its own) — the shape doubleCutElim removes as a single unit
      // (applyDoubleCutElim deletes the passed region AND its lone child
      // together, promoting the child's own children up two levels), so
      // one call collapses both extra negations at once.
      let diagram = formulaToDiagram('∀P:o. ¬¬¬(P ∧ ¬P)')
      const body = findBodyRegion(diagram)
      let target = findDoubleCutToNormalize(diagram, body)
      expect(target, 'expected an eligible double-cut region in ¬¬¬(P ∧ ¬P)').not.toBeNull()
      let steps = 0
      while (target !== null) {
        diagram = applyStep(diagram, { rule: 'doubleCutElim', region: target }, EMPTY_PROOF_CONTEXT, 'forward')
        steps += 1
        target = findDoubleCutToNormalize(diagram, body)
      }
      expect(steps).toBe(1)
      expect(sameDiagram(diagram, formulaToDiagram('∀P:o. ¬(P ∧ ¬P)'))).toBe(true)
    },
  )
})

describe('findDuplicateToNormalize', () => {
  it(
    'eliminates the duplicate P in ¬(P ∧ P ∧ ¬P) down to ¬(P ∧ ¬P) in exactly one deiteration',
    () => {
      // formulaToDiagram draws exactly what is written — it does not itself
      // dedupe — so this genuinely produces two distinct atom nodes heading
      // the same wire in the same region (verified by reading the diagram
      // directly: both P occurrences in 'P ∧ P ∧ ¬P' sit as sibling atom
      // nodes in the cut region that is the ¬'s argument).
      let diagram = formulaToDiagram('∀P:o. ¬(P ∧ P ∧ ¬P)')
      const body = findBodyRegion(diagram)
      let target = findDuplicateToNormalize(diagram, body)
      expect(target, 'expected a same-region duplicate in ¬(P ∧ P ∧ ¬P)').not.toBeNull()
      let steps = 0
      while (target !== null) {
        diagram = applyStep(diagram, deiterationStep(diagram, target), EMPTY_PROOF_CONTEXT, 'forward')
        steps += 1
        target = findDuplicateToNormalize(diagram, body)
      }
      expect(steps).toBe(1)
      expect(sameDiagram(diagram, formulaToDiagram('∀P:o. ¬(P ∧ ¬P)'))).toBe(true)
    },
  )
  it('finds no duplicate in a theorem with no same-region repeat (broken-finder check)', () => {
    // If the finder always returned a hit, this would wrongly pass the
    // "not null" branch above too; this case pins the negative side down —
    // a genuinely duplicate-free theorem must report null.
    const diagram = formulaToDiagram('∀P Q:o. ¬(P ∧ ¬Q)')
    expect(findDuplicateToNormalize(diagram, findBodyRegion(diagram))).toBeNull()
  })
  it('does not flag two distinct cuts with different underlying wires as duplicates', () => {
    // ¬(¬P ∧ ¬Q): two sibling cuts, same SHAPE (¬atom) but different wires —
    // must not be treated as a duplicate.
    const diagram = formulaToDiagram('∀P Q:o. ¬(¬P ∧ ¬Q)')
    expect(findDuplicateToNormalize(diagram, findBodyRegion(diagram))).toBeNull()
  })
  it('finds a duplicate cut pair (¬P ∧ ¬P) and normalizes it to ¬P', () => {
    let diagram = formulaToDiagram('∀P:o. ¬(¬P ∧ ¬P)')
    const body = findBodyRegion(diagram)
    let target = findDuplicateToNormalize(diagram, body)
    expect(target, 'expected the duplicate ¬P cut pair to be found').not.toBeNull()
    let steps = 0
    while (target !== null) {
      diagram = applyStep(diagram, deiterationStep(diagram, target), EMPTY_PROOF_CONTEXT, 'forward')
      steps += 1
      target = findDuplicateToNormalize(diagram, body)
    }
    expect(steps).toBe(1)
    expect(sameDiagram(diagram, formulaToDiagram('∀P:o. ¬¬P'))).toBe(true)
  })
})
