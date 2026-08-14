import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { containsDoubleNegation, containsDuplicateConjunct, isTautology, type PropFormula } from '../../src/generate/prop/formula'
import { samplePropFormula } from '../../src/generate/prop/sample'
import { isMinimalTautology, shrinkToCore, simplify, weakenings } from '../../src/generate/prop/shrink'

const P: PropFormula = { kind: 'atom', index: 0 }
const Q: PropFormula = { kind: 'atom', index: 1 }
const TOP: PropFormula = { kind: 'top' }
const BOT: PropFormula = { kind: 'bot' }
const not = (body: PropFormula): PropFormula => ({ kind: 'not', body })
const and = (left: PropFormula, right: PropFormula): PropFormula => ({ kind: 'and', left, right })
const NONCONTRADICTION = not(and(P, not(P)))

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

describe('shrinkToCore', () => {
  it('removes a junk conjunct-under-negation from the noncontradiction core', () => {
    // ¬(P ∧ ¬P ∧ Q): Q is dead weight (negative occurrence → ⊤ keeps validity).
    const junky = not(and(and(P, not(P)), Q))
    expect(isTautology(junky, 2)).toBe(true)
    expect(shrinkToCore(junky, 2)).toEqual(NONCONTRADICTION)
  })
  it('rejects non-tautology input loudly', () => {
    expect(() => shrinkToCore(P, 1)).toThrow(/not a tautology/)
  })
  it('property: every shrunk sampled tautology is minimal', () => {
    const rng = seededRng(2026)
    let tautologies = 0
    for (let round = 0; round < 400 && tautologies < 25; round += 1) {
      const sampled = samplePropFormula(10, 3, rng)
      if (!isTautology(sampled, 3)) continue
      tautologies += 1
      const core = shrinkToCore(sampled, 3)
      expect(isMinimalTautology(core, 3), `core of sample ${round} not minimal`).toBe(true)
      expect(containsDoubleNegation(core), `core of sample ${round} contains ¬¬`).toBe(false)
      expect(containsDuplicateConjunct(core), `core of sample ${round} contains a duplicate conjunct`).toBe(false)
    }
    expect(tautologies, 'sampler produced too few tautologies for the property test').toBeGreaterThan(10)
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
