import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import {
  atomName,
  connectiveCount,
  containsDoubleNegation,
  evaluate,
  isTautology,
  printFormula,
  printTheorem,
  usedAtoms,
  type PropFormula,
} from '../../src/generate/prop/formula'
import { parseFormula } from '../../src/formula/parse'
import type { Formula } from '../../src/formula/syntax'

const P: PropFormula = { kind: 'atom', index: 0 }
const Q: PropFormula = { kind: 'atom', index: 1 }
const not = (body: PropFormula): PropFormula => ({ kind: 'not', body })
const and = (left: PropFormula, right: PropFormula): PropFormula => ({ kind: 'and', left, right })
// ¬(P ∧ ¬P) — the law of noncontradiction, the running example of the spec.
const NONCONTRADICTION = not(and(P, not(P)))

/** Convert a parsed Formula body back to PropFormula, inverting atomName. */
function fromParsed(formula: Formula): PropFormula {
  switch (formula.kind) {
    case 'atom': {
      const index = [...Array(64).keys()].find((i) => atomName(i) === formula.name)
      if (index === undefined) throw new Error(`unexpected atom name '${formula.name}'`)
      return { kind: 'atom', index }
    }
    case 'not':
      return { kind: 'not', body: fromParsed(formula.body) }
    case 'and':
      return { kind: 'and', left: fromParsed(formula.left), right: fromParsed(formula.right) }
    default:
      throw new Error(`unexpected connective '${formula.kind}' in printed output`)
  }
}

describe('seededRng', () => {
  it('is deterministic for a fixed seed and stays within [0,1)', () => {
    const a = seededRng(42)
    const b = seededRng(42)
    const streamA = Array.from({ length: 100 }, () => a())
    const streamB = Array.from({ length: 100 }, () => b())
    expect(streamA).toEqual(streamB)
    for (const value of streamA) {
      expect(value).toBeGreaterThanOrEqual(0)
      expect(value).toBeLessThan(1)
    }
    expect(new Set(streamA).size).toBeGreaterThan(90)
  })
})

describe('evaluate / isTautology', () => {
  it('evaluates the truth table of ¬(P ∧ ¬P)', () => {
    expect(evaluate(NONCONTRADICTION, [true])).toBe(true)
    expect(evaluate(NONCONTRADICTION, [false])).toBe(true)
    expect(isTautology(NONCONTRADICTION, 1)).toBe(true)
  })
  it('rejects non-tautologies and evaluates constants', () => {
    expect(isTautology(P, 1)).toBe(false)
    expect(isTautology(and(P, not(P)), 1)).toBe(false)
    expect(evaluate({ kind: 'top' }, [])).toBe(true)
    expect(evaluate({ kind: 'bot' }, [])).toBe(false)
    // Peirce-ish two-atom tautology: ¬(¬(P∧Q) ∧ P ∧ Q) — spelled with binary ands.
    expect(isTautology(not(and(and(not(and(P, Q)), P), Q)), 2)).toBe(true)
  })
  it('throws loudly on an unassigned atom', () => {
    expect(() => evaluate(Q, [true])).toThrow(/atom 1/)
  })
})

describe('counting helpers', () => {
  it('counts connectives and used atoms', () => {
    expect(connectiveCount(NONCONTRADICTION)).toBe(3)
    expect(connectiveCount(P)).toBe(0)
    expect([...usedAtoms(and(P, and(Q, P)))].sort()).toEqual([0, 1])
  })
})

describe('containsDoubleNegation', () => {
  it('detects a direct not(not(_))', () => {
    expect(containsDoubleNegation(not(not(P)))).toBe(true)
  })
  it('is false for a single negation beside its atom', () => {
    expect(containsDoubleNegation(not(and(P, not(P))))).toBe(false)
  })
  it('detects a double negation nested under ∧', () => {
    expect(containsDoubleNegation(and(P, not(not(Q))))).toBe(true)
  })
  it('is false for two single negations side by side', () => {
    expect(containsDoubleNegation(not(and(not(P), not(Q))))).toBe(false)
  })
})

describe('printing', () => {
  it('names atoms as letters then numbered fallbacks', () => {
    expect(atomName(0)).toBe('P')
    expect(atomName(1)).toBe('Q')
    expect(atomName(7)).toBe('W')
    expect(atomName(8)).toBe('P8')
  })
  it('round-trips through parseFormula with correct precedence', () => {
    const cases: PropFormula[] = [
      NONCONTRADICTION,
      and(P, and(Q, P)),          // right-nested and needs parens
      and(and(P, Q), P),          // left-nested and needs none
      not(not(P)),
      and(not(P), not(and(P, Q))),
    ]
    for (const formula of cases) {
      const printed = printTheorem(formula)
      const parsed = parseFormula(printed)
      if (parsed.kind !== 'quantifier' || parsed.quantifier !== 'forall') {
        throw new Error(`printed theorem did not parse as a ∀: ${printed}`)
      }
      expect(fromParsed(parsed.body)).toEqual(formula)
    }
  })
  it('quantifies exactly the used atoms in index order', () => {
    expect(printTheorem(NONCONTRADICTION)).toBe('∀P:o. ¬(P ∧ ¬P)')
    expect(printTheorem(and(not(Q), Q)).startsWith('∀Q:o.')).toBe(true)
  })
  it('refuses to print constants or an atom-free formula', () => {
    expect(() => printFormula({ kind: 'top' })).toThrow(/constant/)
    expect(() => printTheorem(not({ kind: 'bot' }))).toThrow(/no atoms/)
  })
})
