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
  it('solves Peirce\'s law deletion-only, via the rescued pin-bundle candidate class', () => {
    // ((P→Q)→P)→P in ¬/∧ form — folklore's classic insertion-requiring
    // theorem, but that folklore is a claim about FORWARD derivations. Read
    // forward, the backward deletion alphabet {erasure(negative),
    // deiteration, doubleCutElim, vacuity-delete} mirrors to
    // {doubleCutIntro, insertion-into-negative-region, iteration,
    // vacuity-insert} — backward erasure of a negative-region selection IS
    // forward insertion. So "Peirce requires insertion" never actually
    // implied "Peirce has no deletion-only backward proof"; the spec's
    // testing-section premise conflated the two directions. Verified by
    // hand-replaying the returned steps via literal applyStep calls down to
    // the blank sheet.
    //
    // This is also the regression pin for the alphabet-hole fix itself:
    // step 1 of the found proof is `erasure` of a cut-selection that
    // strands a wire below the two-end floor — exactly the
    // ScopePreservationError-raising candidate class the enumerator used to
    // drop and now emits, rescued here by the search's auto-pin bundle.
    const peirce = formulaToDiagram('∀P Q:o. ¬(¬(¬(P ∧ ¬Q) ∧ ¬P) ∧ ¬P)')
    const outcome = minimalProofSearch(peirce, DEFAULT_SEARCH_FUEL)
    if (outcome.status !== 'solved') throw new Error(`expected a solve, got ${JSON.stringify(outcome)}`)
    expect(outcome.mode).toBe('deletion-only')
    expect(outcome.length).toBe(8)
    expect(outcome.requires).toEqual(['iteration', 'doubleCut'])
  })
  it('reports an honest phase-2 fuel bound on a non-theorem (the exhausted path)', () => {
    // The search only ever meets tautologies in production (generation
    // rejects non-tautologies before the search runs), but the honest
    // fuel-exhausted fallback path still needs end-to-end coverage, and a
    // real tautology may never exercise it (see the Peirce case above,
    // which turned out solvable deletion-only). A non-theorem is the one
    // input guaranteed to: soundness makes the blank sheet unreachable, so
    // phase 1's complete BFS proves no deletion-only proof exists, and
    // phase 2 must burn its entire fuel budget without solving.
    const nonTheorem = formulaToDiagram('∀P:o. P')
    const outcome = minimalProofSearch(nonTheorem, 150)
    if (outcome.status !== 'exhausted') throw new Error(`expected exhaustion, got ${JSON.stringify(outcome)}`)
    expect(outcome.noDeletionOnlyProof).toBe(true)
    expect(outcome.noProofWithin).toBeGreaterThanOrEqual(0)
  })
  it('solves small generated problems from both families end to end', () => {
    const shrink = propShrinkFamily.generate({ atoms: 1, sampleSize: 6, minSize: 2, attempts: 10_000 }, seededRng(5))
    const shrinkOutcome = minimalProofSearch(shrink.diagram, DEFAULT_SEARCH_FUEL)
    expect(shrinkOutcome.status).toBe('solved')
    // Walk moves and search moves are different units (kernel forward walk
    // actions vs. backward search moves, one of which bundles pins) — no
    // theorem relates their counts, so only the solved status is asserted.
    const walk = propWalkFamily.generate({ atoms: 1, length: 4, attempts: 500 }, seededRng(6))
    const walkOutcome = minimalProofSearch(walk.diagram, DEFAULT_SEARCH_FUEL)
    expect(walkOutcome.status).toBe('solved')
  })
})

describe('default-knob sizing (spec: "the default is sized in tests so default-knob problems complete within it")', () => {
  it('family A (prop-shrink) at all-default knobs completes the search within DEFAULT_SEARCH_FUEL', () => {
    const problem = propShrinkFamily.generate({}, seededRng(0))
    const outcome = minimalProofSearch(problem.diagram, DEFAULT_SEARCH_FUEL)
    expect(outcome.status === 'solved' || outcome.status === 'exhausted').toBe(true)
  })
  it(
    'family B (prop-walk) at all-default knobs generates and completes the search within DEFAULT_SEARCH_FUEL',
    () => {
      // Walk length's default was lowered from 12 to 8 for exactly this
      // reason (see the comment on propWalkFamily's knobs): at 12, this
      // same measurement (10 seeds) took 0.8-28.8s per seed and one seed
      // exceeded the attempt cap outright. At 8, 10 seeds all generated in
      // 0.1-4.3s — this per-test 10s timeout follows the existing
      // precedent for measured-necessary generator tests.
      const problem = propWalkFamily.generate({}, seededRng(0))
      const outcome = minimalProofSearch(problem.diagram, DEFAULT_SEARCH_FUEL)
      expect(outcome.status === 'solved' || outcome.status === 'exhausted').toBe(true)
    },
    10_000,
  )
})
