import { describe, expect, it } from 'vitest'

import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { parseFormula } from '../../src/formula/parse'
import { FormulaError, type Formula } from '../../src/formula/syntax'

const EXAMPLE_SOURCE = '∀ Z : i → o. ∀ S : i → i → o. ∀ n m. Z(n) ∧ S(n, m)'

function expectQuantifier(formula: Formula, quantifier: 'exists' | 'forall', name: string): Extract<Formula, { kind: 'quantifier' }> {
  expect(formula.kind).toBe('quantifier')
  if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
  expect(formula.quantifier).toBe(quantifier)
  expect(formula.binders).toHaveLength(1)
  expect(formula.binders[0]!.name).toBe(name)
  return formula
}

describe('parseFormula', () => {
  it('parses the typed Unicode example with grouped individual binders', () => {
    const outer = expectQuantifier(parseFormula(EXAMPLE_SOURCE), 'forall', 'Z')
    expect(outer.binders[0]!.sig).toEqual(relSig([IOTA]))

    const second = expectQuantifier(outer.body, 'forall', 'S')
    expect(second.binders[0]!.sig).toEqual(relSig([IOTA, IOTA]))

    expect(second.body.kind).toBe('quantifier')
    if (second.body.kind !== 'quantifier') throw new Error('expected grouped quantifier')
    expect(second.body.binders.map((binder) => binder.name)).toEqual(['n', 'm'])
    expect(second.body.binders.map((binder) => binder.sig)).toEqual([IOTA, IOTA])
  })

  it('makes implication right-associative and conjunction tighter', () => {
    const formula = parseFormula('∀ A B C : o. A -> B ∧ C => A')
    expect(formula.kind).toBe('quantifier')
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expect(formula.body.kind).toBe('implies')
    if (formula.body.kind !== 'implies') throw new Error('expected implication')
    expect(formula.body.left.kind).toBe('atom')
    expect(formula.body.right.kind).toBe('implies')
    if (formula.body.right.kind !== 'implies') throw new Error('expected nested implication')
    expect(formula.body.right.left.kind).toBe('and')
  })

  it('accepts ASCII quantifiers, implications, and Unicode conjunction', () => {
    expect(() => parseFormula('forall P : i -> o. exists x. P(x)')).not.toThrow()
    expect(() => parseFormula('∀ P : i => o. ∃ x. P(x) ∧ P(x)')).not.toThrow()
  })

  it('returns immutable syntax', () => {
    const formula = parseFormula(EXAMPLE_SOURCE)
    expect(Object.isFrozen(formula)).toBe(true)
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expect(Object.isFrozen(formula.binders)).toBe(true)
    expect(Object.isFrozen(formula.binders[0]!)).toBe(true)
    const grouped = formula.body.body
    if (grouped.kind !== 'quantifier' || grouped.body.kind !== 'and') throw new Error('expected grouped conjunction')
    if (grouped.body.left.kind !== 'atom') throw new Error('expected atom')
    expect(Object.isFrozen(grouped.body.left.args)).toBe(true)
    expect(Object.isFrozen(grouped.body.left.span)).toBe(true)
  })

  it('validates argument signatures and permits nested lexical shadowing', () => {
    expect(() => parseFormula('∀ P : i → o. ∀ Q : o → o. ∀ x. P(Q)')).toThrow(FormulaError)
    expect(() => parseFormula('∀ P : i → o. ∀ x. ∃ P : o. P')).not.toThrow()
  })

  it.each([
    ['∀ x. P(x) @', 11],
    ['∀ x.', 5],
    ['∀ x x. x', 5],
    ['∀ f : i → i. f', 11],
    ['∀ x. Missing(x)', 6],
  ])('rejects invalid input at its source location', (source, column) => {
    expect(() => parseFormula(source)).toThrow(FormulaError)
    expect(() => parseFormula(source)).toThrow(new RegExp(`line 1, column ${column}`))
  })
})
