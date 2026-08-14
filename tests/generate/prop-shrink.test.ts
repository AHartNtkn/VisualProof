import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { containsDoubleNegation, containsDuplicateConjunct, isTautology, type PropFormula } from '../../src/generate/prop/formula'
import { samplePropFormula } from '../../src/generate/prop/sample'
import {
  containsDeiterationRedex,
  isMinimalTautology,
  normalizeDeiterations,
  normalizeToFixpoint,
  shrinkToCore,
  simplify,
  weakenings,
} from '../../src/generate/prop/shrink'
import { parseFormula } from '../../src/formula/parse'
import type { Formula } from '../../src/formula/syntax'

const P: PropFormula = { kind: 'atom', index: 0 }
const Q: PropFormula = { kind: 'atom', index: 1 }
const D: PropFormula = { kind: 'atom', index: 3 }
const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }
const not = (body: PropFormula): PropFormula => ({ kind: 'not', body })
const and = (left: PropFormula, right: PropFormula): PropFormula => ({ kind: 'and', left, right })
const NONCONTRADICTION = not(and(P, not(P)))

/** Parse a ∀-quantified prop-language source string into a PropFormula,
 *  mapping atom names by the quantifier's own binder order (not by
 *  `atomName`, since this fixture spells atoms A/B/C rather than P/Q/R). */
function fromParsed(formula: Formula, names: readonly string[]): PropFormula {
  switch (formula.kind) {
    case 'atom': {
      const index = names.indexOf(formula.name)
      if (index === -1) throw new Error(`unexpected atom name '${formula.name}'`)
      return { kind: 'atom', index }
    }
    case 'not':
      return { kind: 'not', body: fromParsed(formula.body, names) }
    case 'and':
      return { kind: 'and', left: fromParsed(formula.left, names), right: fromParsed(formula.right, names) }
    default:
      throw new Error(`unexpected connective '${formula.kind}' in a ¬/∧ fixture`)
  }
}

function parseProp(source: string): PropFormula {
  const parsed = parseFormula(source)
  if (parsed.kind !== 'quantifier') throw new Error('fixture source did not parse as a ∀-quantified formula')
  return fromParsed(parsed.body, parsed.binders.map((binder) => binder.name))
}

// The distributivity identity ¬(¬(A∧¬(B∧C)) ∧ ¬(¬(A∧¬B)∧¬(A∧¬C))) — a
// deiteration-normalization FIXED POINT (verified by hand by the user who
// requested this scope extension, and confirmed here computationally): no
// occurrence has a structurally identical copy available in its own area or
// any enclosing area, so normalizeDeiterations/normalizeToFixpoint/
// shrinkToCore must all leave it byte-for-byte unchanged. This is the
// CRITICAL regression guarding against an over-eager normalizer.
const DISTRIB = parseProp('∀A B C:o. ¬(¬(A ∧ ¬(B ∧ C)) ∧ ¬(¬(A ∧ ¬B) ∧ ¬(A ∧ ¬C)))')

describe('simplify', () => {
  it('eliminates constants with the four identities', () => {
    expect(simplify(and(TOP, P))).toEqual(P)
    expect(simplify(and(P, BOT))).toEqual(BOT)
    expect(simplify(not(TOP))).toEqual(BOT)
    expect(simplify(not(not(BOT)))).toEqual(BOT)
    expect(simplify(and(not(BOT), and(TOP, Q)))).toEqual(Q)
  })
  it('leaves constant-free formulas untouched', () => {
    expect(simplify(NONCONTRADICTION)).toEqual(NONCONTRADICTION)
  })
  it('collapses doubled negation at every depth', () => {
    expect(simplify(not(not(P)))).toEqual(P)
    expect(simplify(not(not(not(not(P)))))).toEqual(P)
    expect(simplify(not(not(not(P))))).toEqual(not(P))
  })
  it('collapses doubled negation created by constant elimination', () => {
    // ¬(⊤ ∧ ¬P) simplifies its body to ¬P (⊤∧¬P≡¬P), leaving ¬¬P, which
    // must then collapse to P rather than surviving as a doubled negation.
    expect(simplify(not(and(TOP, not(P))))).toEqual(P)
  })
  it('dedupes a directly repeated conjunct', () => {
    expect(simplify(and(P, P))).toEqual(P)
  })
  it('dedupes a non-adjacent duplicate across a flattened ∧-chain', () => {
    expect(simplify(and(and(P, Q), P))).toEqual(and(P, Q))
  })
  it('dedupes a duplicate nested under ¬', () => {
    expect(simplify(not(and(P, P)))).toEqual(not(P))
  })
  it('dedupes after the ¬¬ collapse (interaction case)', () => {
    // and(P, not(not(P))): not(not(P)) collapses to P before dedupe sees the
    // conjunct list, so the ∧-chain is [P, P] and reduces to P alone.
    expect(simplify(and(P, not(not(P))))).toEqual(P)
  })
  it('dedupes a leaf that only becomes ∧-shaped through its OWN simplification', () => {
    // ¬¬(P∧Q) is not ∧-shaped in the RAW tree — it's a `not` node — so a
    // flatten-then-simplify-leaves order (flatten the raw shape, THEN
    // simplify each leaf) never re-flattens what that leaf's simplification
    // exposes. and(¬¬(P∧Q), and(P,R)): the ¬¬ collapses to and(P,Q), which
    // must be re-flattened and compared against the OTHER branch's P for
    // this to dedupe correctly, one call, no fixed retry count.
    const result = simplify(and(not(not(and(P, Q))), and(P, D)))
    expect(result).toEqual(and(and(P, Q), D))
    expect(containsDuplicateConjunct(result)).toBe(false)
  })
  it('dedupes across TWO nested levels of ∧-exposing ¬¬ collapse (unbounded-depth case)', () => {
    // The exposed and(P,Q) inside the ¬¬ itself contains ANOTHER ¬¬-wrapped
    // and — flattening it requires simplifying its own children, which in
    // turn exposes a THIRD level (P,Q) needing yet another round. No single
    // fixed number of flatten/simplify alternations suffices in general;
    // the fix must recurse to an actual fixpoint, not a bounded retry count.
    const nested = and(not(not(and(not(not(and(P, Q))), D))), P)
    const result = simplify(nested)
    expect(result).toEqual(and(and(P, Q), D))
    expect(containsDuplicateConjunct(result)).toBe(false)
  })
  it(
    'property: output never contains a duplicate conjunct, over many sampled formulas (single call — ' +
    'this is the exact assertion that would have caught the incomplete-flatten bug; final-core checks alone missed it)',
    () => {
      // Reviewer's repro methodology exactly: default family-A sample knobs
      // (atoms 3, sample size 12 connectives), seed 2026, 20,000 samples.
      // Measured with the pre-fix and-case: 22% of these single-call
      // outputs carried a residual duplicate.
      const rng = seededRng(2026)
      for (let round = 0; round < 20_000; round += 1) {
        const sampled = samplePropFormula(12, 3, rng)
        const result = simplify(sampled)
        expect(containsDuplicateConjunct(result), `simplify(sample ${round}) contains a duplicate conjunct`).toBe(false)
      }
    },
  )
})

describe('weakenings', () => {
  it('substitutes ⊥ at positive and ⊤ at negative occurrences', () => {
    // P ∧ ¬Q at positive root has exactly four occurrences:
    //   root (positive) → ⊥;  P (positive) → ⊥;
    //   ¬Q (positive) → ⊥;  Q (negative, under one ¬) → ⊤.
    const results = weakenings(and(P, not(Q)))
    expect(results).toHaveLength(4)
    expect(results).toContainEqual(BOT)
    expect(results).toContainEqual(and(BOT, not(Q)))
    expect(results).toContainEqual(and(P, BOT))
    expect(results).toContainEqual(and(P, not(TOP)))
  })
})

describe('normalizeArea (via normalizeDeiterations)', () => {
  it('leaves a formula with no redex anywhere untouched', () => {
    expect(normalizeDeiterations(and(P, Q))).toEqual(and(P, Q))
  })
  it('drops an atom justified by an ancestor-area sibling, one pass', () => {
    // ¬(P ∧ ¬(P ∧ Q)): the inner P (two cuts deep) has an identical copy P
    // one area out (a sibling of the cut it sits inside) — an ENCLOSING
    // area, so it justifies the inner copy under EG-style deiteration
    // containment (crossing the cut boundary, unlike erasure/insertion,
    // which are polarity-gated). One pass reduces this exactly to ¬(P∧¬Q),
    // with no residual ⊤/BOT artifact since Q survives as the inner area's
    // remaining member.
    const f = not(and(P, not(and(P, Q))))
    expect(normalizeDeiterations(f)).toEqual(not(and(P, not(Q))))
  })
  it('drops a same-area sibling (Task 13\'s original case), still supported', () => {
    expect(normalizeDeiterations(and(P, P))).toEqual(P)
  })
  it('a cut can never justify a deiteration inside itself', () => {
    // ¬(¬P): the cut ¬P's own body P has no OTHER context available (the
    // cut itself is excluded from its own recursion's context), so this is
    // NOT a redex — it must survive unchanged.
    expect(normalizeDeiterations(not(not(P)))).toEqual(not(not(P)))
  })
  it('reduces ¬(P∧¬P) toward ⊤ across normalizeDeiterations + simplify (one pass leaves a ¬⊤ residue)', () => {
    // One pass alone leaves ¬(P ∧ ¬⊤) — the inner P is justified by the
    // OUTER P (an enclosing-area sibling), same mechanism as the ancestor
    // case above; simplify then collapses ¬⊤→⊥, making the whole ∧ collapse
    // to ⊥, and the outer ¬⊥→⊤.
    expect(normalizeDeiterations(NONCONTRADICTION)).toEqual(not(and(P, not(TOP))))
    expect(simplify(normalizeDeiterations(NONCONTRADICTION))).toEqual(TOP)
  })
})

describe('normalizeToFixpoint', () => {
  it('reduces ¬(P∧¬P) all the way to ⊤', () => {
    // The law of non-contradiction has a well-known short EG proof
    // (deiterate the inner P, then double-cut-eliminate) — search.test.ts's
    // hand-verified 5-step deletion-only backward proof of ∀P:o.¬(P∧¬P)
    // documents the SAME deiteration step this is the formula-level mirror
    // of. Collapsing all the way to ⊤ here is correct grading, not a bug.
    expect(normalizeToFixpoint(NONCONTRADICTION)).toEqual(TOP)
  })
  it('leaves the distributivity fixed point byte-for-byte unchanged', () => {
    expect(normalizeToFixpoint(DISTRIB)).toEqual(DISTRIB)
  })
  it('is idempotent at a fixed point', () => {
    const once = normalizeToFixpoint(DISTRIB)
    expect(normalizeToFixpoint(once)).toEqual(once)
  })
})

describe('containsDeiterationRedex', () => {
  it('is false for the distributivity fixed point', () => {
    expect(containsDeiterationRedex(DISTRIB)).toBe(false)
  })
  it('is true for ¬(P∧¬P) (an ancestor-justified redex)', () => {
    expect(containsDeiterationRedex(NONCONTRADICTION)).toBe(true)
  })
  it('is true for a same-area duplicate (Task 13\'s original case)', () => {
    expect(containsDeiterationRedex(and(P, P))).toBe(true)
  })
  it('is false for two distinct conjuncts', () => {
    expect(containsDeiterationRedex(and(P, Q))).toBe(false)
  })
})

describe('shrinkToCore', () => {
  describe('fullDeiteration: false (default) — same-region-only repair (Task 13, unchanged)', () => {
    it('removes a junk conjunct-under-negation from the noncontradiction core', () => {
      // ¬(P ∧ ¬P ∧ Q): Q is dead weight (negative occurrence → ⊤ keeps
      // validity). With the flag off, shrinkToCore never runs
      // normalizeToFixpoint, so the P∧¬P sub-pattern does NOT collapse via
      // ancestor-justified deiteration (see the flag-on describe block
      // below for that case) — only weakening applies, landing exactly on
      // the noncontradiction core, matching Task 13's original behavior.
      const junky = not(and(and(P, not(P)), Q))
      expect(isTautology(junky, 2)).toBe(true)
      expect(shrinkToCore(junky, 2, false)).toEqual(NONCONTRADICTION)
    })
    it('property: every shrunk sampled tautology is minimal, ¬¬-free, and same-region-duplicate-free', () => {
      const rng = seededRng(2026)
      let tautologies = 0
      for (let round = 0; round < 400 && tautologies < 25; round += 1) {
        const sampled = samplePropFormula(10, 3, rng)
        if (!isTautology(sampled, 3)) continue
        tautologies += 1
        const core = shrinkToCore(sampled, 3, false)
        expect(isMinimalTautology(core, 3), `core of sample ${round} not minimal`).toBe(true)
        expect(containsDoubleNegation(core), `core of sample ${round} contains ¬¬`).toBe(false)
        expect(containsDuplicateConjunct(core), `core of sample ${round} contains a duplicate conjunct`).toBe(false)
      }
      expect(tautologies, 'sampler produced too few tautologies for the property test').toBeGreaterThan(10)
    })
  })
  describe('fullDeiteration: true (opt-in) — ancestor-justified repair', () => {
    it('collapses ¬(P∧¬P∧Q) all the way to ⊤, not to the noncontradiction core', () => {
      // With the flag on, the inner P∧¬P sub-pattern itself collapses
      // (identical mechanism to normalizeToFixpoint(NONCONTRADICTION)
      // above) before weakening is even needed, taking Q down with it via
      // simplify's ⊥-short-circuit — correct grading for this mode, and
      // exactly why it defaults off (see the family knob comment).
      const junky = not(and(and(P, not(P)), Q))
      expect(isTautology(junky, 2)).toBe(true)
      expect(shrinkToCore(junky, 2, true)).toEqual(TOP)
    })
    it('still uses WEAKENING for dead weight that has no deiteration redex', () => {
      // ¬(¬DISTRIB ∧ D): DISTRIB is a tautology, so ¬DISTRIB is unsatisfiable,
      // so ¬DISTRIB∧D is always false regardless of D, so the whole formula is
      // a tautology with D as pure dead weight — but D is a FRESH atom with no
      // structural duplicate anywhere, so deiteration can never touch it; only
      // weakening (D → ⊤, since D sits at negative polarity here) removes it,
      // leaving ¬¬DISTRIB → (¬¬ collapse) → DISTRIB exactly.
      const junky = not(and(not(DISTRIB), D))
      expect(isTautology(junky, 4)).toBe(true)
      expect(shrinkToCore(junky, 4, true)).toEqual(DISTRIB)
    })
    it('property: every shrunk sampled tautology is either fully collapsed (⊤) or minimal and redex-free', () => {
      const rng = seededRng(2026)
      let tautologies = 0
      let fullyCollapsed = 0
      for (let round = 0; round < 400 && tautologies < 25; round += 1) {
        const sampled = samplePropFormula(10, 3, rng)
        if (!isTautology(sampled, 3)) continue
        tautologies += 1
        const core = shrinkToCore(sampled, 3, true)
        if (core.kind === 'top') {
          // A legitimate outcome under full ancestor-justified deiteration
          // (e.g. any sample containing an atom X and ¬X anywhere in a
          // nesting relationship — not just the same area — collapses).
          fullyCollapsed += 1
          continue
        }
        expect(isMinimalTautology(core, 3), `core of sample ${round} not minimal`).toBe(true)
        expect(containsDoubleNegation(core), `core of sample ${round} contains ¬¬`).toBe(false)
        expect(containsDeiterationRedex(core), `core of sample ${round} contains a deiteration redex`).toBe(false)
      }
      expect(tautologies, 'sampler produced too few tautologies for the property test').toBeGreaterThan(10)
      // Measured basis for the flag defaulting off (per the design doc):
      // printed for visibility, not asserted on precisely.
      console.log(`shrinkToCore property test (fullDeiteration:true): ${fullyCollapsed}/${tautologies} samples fully collapsed to ⊤`)
    })
  })
  it.each([false, true])('rejects non-tautology input loudly (fullDeiteration=%s)', (fullDeiteration) => {
    expect(() => shrinkToCore(P, 1, fullDeiteration)).toThrow(/not a tautology/)
  })
})

describe('isMinimalTautology', () => {
  it('accepts the noncontradiction core and rejects padded variants', () => {
    expect(isMinimalTautology(NONCONTRADICTION, 1)).toBe(true)
    expect(isMinimalTautology(not(and(and(P, not(P)), Q)), 2)).toBe(false)
    expect(isMinimalTautology(P, 1)).toBe(false)          // not a tautology
    expect(isMinimalTautology(not(BOT), 0)).toBe(false)   // contains a constant
  })
})
