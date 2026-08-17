import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES } from '../../src/generate'
import {
  findDeiterationRedex,
  findDoubleCutToNormalize,
  findDuplicateToNormalize,
  propWalkFamily,
} from '../../src/generate/walk/family'
import { readPropTheorem } from '../../src/generate/prop/read'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { containsDoubleNegation, containsDuplicateConjunct, usedAtoms } from '../../src/generate/prop/formula'
import { sweepRemovablePins } from '../fixtures/pins'
import { formulaToDiagram } from '../../src/formula'
import { deiterationStep } from '../../src/app/interact/moves'
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
  it('generates certified, minimal, readable theorems (seed batch, fullDeiteration off, default)', () => {
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
    // ~2x headroom over that worst case. fullDeiteration defaults off, so
    // this call is unaffected by the opt-in extension — same-region-only
    // guarantee, hence `containsDuplicateConjunct`, not the stronger
    // `containsDeiterationRedex` the flag-on mode would guarantee.
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
  it(
    'fullDeiteration:1 at a small attempt cap throws the honest attempt-cap error — the measured collapse reality',
    () => {
      // Deliberately NOT testing a flag-on success: findDeiterationRedex's
      // ancestor-justified normalization has the same nearly-unsamplable
      // fixed-point property as family A's (measured directly on this
      // family too — the seed batch that succeeds within 49 attempts at
      // default knobs exhausts 1000 with the flag on). Hunting for a
      // lucky seed would misrepresent that reality; this documents it
      // truthfully instead.
      expect(() => propWalkFamily.generate(
        { atoms: 2, length: 6, attempts: 50, fullDeiteration: 1 },
        seededRng(1),
      )).toThrow(/attempts/)
    },
  )
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
      // the same wire in the same region. Unlike findDeiterationRedex (the
      // opt-in relaxation), this SAME-REGION-ONLY finder does not cascade
      // into the ancestor-justified P-inside-¬P redex, so this reduces
      // cleanly to ¬(P ∧ ¬P) in exactly one step.
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
  it('finds no redex in an ANCESTOR-justified case (that is findDeiterationRedex\'s job, not this finder\'s)', () => {
    // ¬(P ∧ ¬(P ∧ Q)): the inner P is justified only by the OUTER P, an
    // enclosing area, not a same-region sibling — this finder must not
    // find it (see findDeiterationRedex's dedicated test for the same
    // fixture, which DOES find it).
    const diagram = formulaToDiagram('∀P Q:o. ¬(P ∧ ¬(P ∧ Q))')
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

describe('findDeiterationRedex', () => {
  it(
    'eliminates a same-region duplicate P in ¬(P ∧ P ∧ Q) down to ¬(P ∧ Q) in exactly one deiteration',
    () => {
      // formulaToDiagram draws exactly what is written — it does not itself
      // dedupe — so this genuinely produces two distinct atom nodes heading
      // the same wire in the same region (Task 13's same-region case,
      // still covered as the special case where the justifier is a
      // sibling rather than an ancestor). Q (not ¬P — see the cascading
      // test below) keeps this a clean single-step case: with no nested
      // cut for the surviving P to additionally justify, there is exactly
      // one redex here, not two.
      let diagram = formulaToDiagram('∀P Q:o. ¬(P ∧ P ∧ Q)')
      const body = findBodyRegion(diagram)
      let target = findDeiterationRedex(diagram, body)
      expect(target, 'expected a same-region duplicate in ¬(P ∧ P ∧ Q)').not.toBeNull()
      let steps = 0
      while (target !== null) {
        diagram = applyStep(diagram, target.step, EMPTY_PROOF_CONTEXT, 'forward')
        steps += 1
        target = findDeiterationRedex(diagram, body)
      }
      expect(steps).toBe(1)
      expect(sameDiagram(diagram, formulaToDiagram('∀P Q:o. ¬(P ∧ Q)'))).toBe(true)
    },
  )
  it(
    'a same-region duplicate can cascade into an ancestor-justified redex, leaving an empty cut',
    () => {
      // ¬(P ∧ P ∧ ¬P): step 1 removes one of the duplicate same-region P
      // atoms (as above). Step 2 finds a SECOND redex the relaxed finder
      // now correctly identifies but the same-region-only version never
      // could: the P inside the ¬P cut is ALSO justified by the surviving
      // P in the enclosing area. Removing it empties the ¬P cut entirely
      // (zero nodes, zero children) — a shape neither this finder (nothing
      // left inside to match) nor findDoubleCutToNormalize (needs exactly
      // one child cut, not zero) can process further. Reading the result
      // back, the empty cut is `¬⊤` (readPropRegion's empty-area
      // convention), which correctly fails isMinimalTautology's
      // containsConstant check — the generator's EXISTING minimality
      // filter already turns this into a walk rejection (not a crash) at
      // the pipeline level; this test just pins the mechanism down
      // directly, at the finder, so a regression here is caught early.
      let diagram = formulaToDiagram('∀P:o. ¬(P ∧ P ∧ ¬P)')
      const body = findBodyRegion(diagram)
      let target = findDeiterationRedex(diagram, body)
      let steps = 0
      while (target !== null) {
        diagram = applyStep(diagram, target.step, EMPTY_PROOF_CONTEXT, 'forward')
        steps += 1
        target = findDeiterationRedex(diagram, body)
      }
      expect(steps).toBe(2)
      const reading = readPropTheorem(diagram)
      expect(isMinimalTautology(reading.formula, reading.wires.length)).toBe(false)
    },
  )
  it(
    'eliminates an ANCESTOR-justified redex: ¬(P ∧ ¬(P ∧ Q)) → ¬(P ∧ ¬Q)',
    () => {
      // The inner P (two cuts deep) has an identical copy P one area OUT
      // (a sibling of the cut it sits inside) — an area that ENCLOSES the
      // inner one, which justifies the removal under EG-style deiteration
      // containment (crossing the cut boundary; unlike erasure/insertion,
      // deiteration is not polarity-gated). This is the formula-level
      // "ancestor-justified" unit test's diagram-level mirror
      // (prop-shrink.test.ts).
      let diagram = formulaToDiagram('∀P Q:o. ¬(P ∧ ¬(P ∧ Q))')
      const body = findBodyRegion(diagram)
      let target = findDeiterationRedex(diagram, body)
      expect(target, 'expected the ancestor-justified inner P to be found').not.toBeNull()
      let steps = 0
      while (target !== null) {
        diagram = applyStep(diagram, target.step, EMPTY_PROOF_CONTEXT, 'forward')
        steps += 1
        target = findDeiterationRedex(diagram, body)
      }
      expect(steps).toBe(1)
      // The deiteration leaves its removal residue (a cap on P's wire at
      // the removal region); the recorder's tidy pass sweeps such ⊤-idle
      // pins after every action, so sweep here the same way.
      expect(sameDiagram(
        sweepRemovablePins(diagram),
        formulaToDiagram('∀P Q:o. ¬(P ∧ ¬Q)'),
      )).toBe(true)
    },
  )
  it('finds no redex in a theorem with no structural repeat (broken-finder check)', () => {
    // If the finder always returned a hit, this would wrongly pass the
    // "not null" branches above too; this case pins the negative side down —
    // a genuinely redex-free theorem must report null.
    const diagram = formulaToDiagram('∀P Q:o. ¬(P ∧ ¬Q)')
    expect(findDeiterationRedex(diagram, findBodyRegion(diagram))).toBeNull()
  })
  it('does not flag two distinct cuts with different underlying wires as duplicates', () => {
    // ¬(¬P ∧ ¬Q): two sibling cuts, same SHAPE (¬atom) but different wires —
    // must not be treated as a duplicate.
    const diagram = formulaToDiagram('∀P Q:o. ¬(¬P ∧ ¬Q)')
    expect(findDeiterationRedex(diagram, findBodyRegion(diagram))).toBeNull()
  })
  it('finds a duplicate cut pair (¬P ∧ ¬P) and normalizes it to ¬P', () => {
    let diagram = formulaToDiagram('∀P:o. ¬(¬P ∧ ¬P)')
    const body = findBodyRegion(diagram)
    let target = findDeiterationRedex(diagram, body)
    expect(target, 'expected the duplicate ¬P cut pair to be found').not.toBeNull()
    let steps = 0
    while (target !== null) {
      diagram = applyStep(diagram, target.step, EMPTY_PROOF_CONTEXT, 'forward')
      steps += 1
      target = findDeiterationRedex(diagram, body)
    }
    expect(steps).toBe(1)
    expect(sameDiagram(diagram, formulaToDiagram('∀P:o. ¬¬P'))).toBe(true)
  })
  it('reports the distributivity fixed point as redex-free', () => {
    // Diagram-level mirror of prop-shrink.test.ts's CRITICAL regression:
    // this identity is a genuine fixed point — no atomic selection anywhere
    // in the body has a justifying copy in its own or any enclosing area.
    const diagram = formulaToDiagram(
      '∀A B C:o. ¬(¬(A ∧ ¬(B ∧ C)) ∧ ¬(¬(A ∧ ¬B) ∧ ¬(A ∧ ¬C)))',
    )
    expect(findDeiterationRedex(diagram, findBodyRegion(diagram))).toBeNull()
  })
})
