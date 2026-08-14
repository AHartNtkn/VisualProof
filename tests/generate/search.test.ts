import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { seededRng } from '../../src/generate/rng'
import { propWalkFamily } from '../../src/generate/walk/family'
import { propShrinkFamily } from '../../src/generate/prop/family'
import { diagramDigest } from '../../src/generate/search/digest'
import { DEFAULT_SEARCH_FUEL, minimalProofSearch } from '../../src/generate/search/search'

describe('diagramDigest', () => {
  it('is invariant under id renaming but separates different shapes', () => {
    const a = formulaToDiagram('∀P:o. ¬(P ∧ ¬P)')
    const b = formulaToDiagram('∀Q:o. ¬(Q ∧ ¬Q)') // isomorphic, different ids
    const c = formulaToDiagram('∀P:o. ¬¬¬(P ∧ ¬P)')
    expect(diagramDigest(a)).toBe(diagramDigest(b))
    expect(diagramDigest(a)).not.toBe(diagramDigest(c))
  })
})

describe('minimalProofSearch', () => {
  it('solves ∀P:o. ¬(P∧¬P) deletion-only in exactly 5 moves, requiring the iteration class', () => {
    // Hand-computed minimal backward proof (team-lead ruling, discrepancy
    // protocol — see task-8-report.md): doubleCutElim(body pair) → deiterate
    // inner P (justified by the relocated outer P) → erase outer P with an
    // auto-pin bundle (the wire's only remaining natural pin is the ∀
    // declaration's own; erasing the last atom strands it below the
    // two-end floor, so the search bundles a pin step with the erasure,
    // exactly as the app's real erase gesture does) → vacuity-delete the
    // now-bare wire → doubleCutElim the shell. All five are deletion moves
    // (auto-pin is bundled into its erasure, not a separate move), so
    // phase 1 solves it; the inner (positive) cut can only be emptied by
    // deiteration, so the iteration class is required; insertion is proven
    // unnecessary.
    const outcome = minimalProofSearch(formulaToDiagram('∀P:o. ¬(P ∧ ¬P)'), DEFAULT_SEARCH_FUEL)
    if (outcome.status !== 'solved') throw new Error(`expected a solve, got ${JSON.stringify(outcome)}`)
    expect(outcome.mode).toBe('deletion-only')
    expect(outcome.length).toBe(5)
    // steps.length may exceed length: the erasure that bundles an auto-pin
    // contributes two ProofSteps (pin, then delete) to that one move.
    expect(outcome.steps.length).toBeGreaterThanOrEqual(5)
    expect(outcome.requires).toContain('iteration')
    expect(outcome.requires).not.toContain('spawn')
  })
  it('proves Peirce\'s law requires insertion, then reports an honest phase-2 result', () => {
    // ((P→Q)→P)→P in ¬/∧ form — the classic insertion-requiring theorem.
    // Phase 1 must exhaust its (small, strictly-shrinking) space without a
    // solve; phase 2 then either solves with the full alphabet or returns
    // the deepest fully-exhausted depth. Tiny fuel keeps this test fast.
    const peirce = formulaToDiagram('∀P Q:o. ¬(¬(¬(P ∧ ¬Q) ∧ ¬P) ∧ ¬P)')
    const outcome = minimalProofSearch(peirce, 200)
    if (outcome.status === 'solved') {
      expect(outcome.mode).toBe('full')
      expect(outcome.requires).toContain('spawn')
    } else {
      expect(outcome.requiresInsertion).toBe(true)
      expect(outcome.noProofWithin).toBeGreaterThanOrEqual(0)
    }
  })
  it('solves small generated problems from both families end to end', () => {
    const shrink = propShrinkFamily.generate({ atoms: 1, sampleSize: 6, minSize: 2, attempts: 10_000 }, seededRng(5))
    const shrinkOutcome = minimalProofSearch(shrink.diagram, DEFAULT_SEARCH_FUEL)
    expect(shrinkOutcome.status).toBe('solved')
    const walk = propWalkFamily.generate({ atoms: 1, length: 4, attempts: 500 }, seededRng(6))
    const walkOutcome = minimalProofSearch(walk.diagram, DEFAULT_SEARCH_FUEL)
    if (walkOutcome.status === 'solved' && walk.walkUpperBound !== undefined) {
      expect(walkOutcome.length).toBeLessThanOrEqual(walk.walkUpperBound + 5)
    } else {
      expect(walkOutcome.status).toBe('solved')
    }
  })
})
