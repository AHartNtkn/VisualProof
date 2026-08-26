import { describe, expect, it } from 'vitest'

import { IOTA, relSig } from '../../src/kernel/diagram/sig'
import { parseFormula } from '../../src/formula/parse'
import {
  FORMULA_UNICODE_SYMBOLS,
  FormulaError,
  type Formula,
} from '../../src/formula/syntax'

const EXAMPLE_SOURCE = '∀ Z : i → o. ∀ S : i → i → o. (∃ z. Z(z)) ⇒ (∀ z. Z(z) ⇒ (∀ P : i → o. ((∀ n. Z(n) ⇒ P(n)) & (∀ n m. (P(n) & S(n, m)) ⇒ P(m))) ⇒ P(z)))'

function expectQuantifier(formula: Formula, quantifier: 'exists' | 'forall', name: string): Extract<Formula, { kind: 'quantifier' }> {
  expect(formula.kind).toBe('quantifier')
  if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
  expect(formula.quantifier).toBe(quantifier)
  expect(formula.binders).toHaveLength(1)
  expect(formula.binders[0]!.name).toBe(name)
  return formula
}

function expectImplication(formula: Formula): Extract<Formula, { kind: 'implies' }> {
  expect(formula.kind).toBe('implies')
  if (formula.kind !== 'implies') throw new Error('expected implication')
  return formula
}

function expectAtom(formula: Formula, name: string, args: readonly string[]): void {
  expect(formula.kind).toBe('atom')
  if (formula.kind !== 'atom') throw new Error('expected atom')
  expect(formula.name).toBe(name)
  expect(formula.args.map((argument) => argument.kind === 'reference' ? argument.name : argument.kind)).toEqual(args)
}

function expectEquality(formula: Formula, operands: readonly string[]): void {
  expect(formula.kind).toBe('equality')
  if (formula.kind !== 'equality') throw new Error('expected equality')
  expect(formula.operands.map((operand) => operand.kind === 'reference' ? operand.name : operand.kind)).toEqual(operands)
  expect(Object.isFrozen(formula.operands)).toBe(true)
}

describe('parseFormula', () => {
  it('publishes every accepted Unicode formula symbol in reading order', () => {
    expect(FORMULA_UNICODE_SYMBOLS.map(({ symbol }) => symbol))
      .toEqual(['∀', '∃', '¬', '∧', '∨', '→', '⇒', '↔', 'λ'])
  })

  it('parses the typed Unicode example with grouped individual binders', () => {
    const outer = expectQuantifier(parseFormula(EXAMPLE_SOURCE), 'forall', 'Z')
    expect(outer.binders[0]!.sig).toEqual(relSig([IOTA]))

    const second = expectQuantifier(outer.body, 'forall', 'S')
    expect(second.binders[0]!.sig).toEqual(relSig([IOTA, IOTA]))

    const outerImplication = expectImplication(second.body)
    const existentialZ = expectQuantifier(outerImplication.left, 'exists', 'z')
    expect(existentialZ.binders[0]!.sig).toEqual(IOTA)
    expectAtom(existentialZ.body, 'Z', ['z'])

    const universalZ = expectQuantifier(outerImplication.right, 'forall', 'z')
    expect(universalZ.binders[0]!.sig).toEqual(IOTA)
    const universalZImplication = expectImplication(universalZ.body)
    expectAtom(universalZImplication.left, 'Z', ['z'])

    const predicate = expectQuantifier(universalZImplication.right, 'forall', 'P')
    expect(predicate.binders[0]!.sig).toEqual(relSig([IOTA]))
    const predicateImplication = expectImplication(predicate.body)
    expect(predicateImplication.left.kind).toBe('and')
    if (predicateImplication.left.kind !== 'and') throw new Error('expected induction conjunction')

    const base = expectQuantifier(predicateImplication.left.left, 'forall', 'n')
    expect(base.binders[0]!.sig).toEqual(IOTA)
    const baseImplication = expectImplication(base.body)
    expectAtom(baseImplication.left, 'Z', ['n'])
    expectAtom(baseImplication.right, 'P', ['n'])

    const step = predicateImplication.left.right
    expect(step.kind).toBe('quantifier')
    if (step.kind !== 'quantifier') throw new Error('expected grouped quantifier')
    expect(step.quantifier).toBe('forall')
    expect(step.binders.map((binder) => binder.name)).toEqual(['n', 'm'])
    expect(step.binders.map((binder) => binder.sig)).toEqual([IOTA, IOTA])
    const stepImplication = expectImplication(step.body)
    expect(stepImplication.left.kind).toBe('and')
    if (stepImplication.left.kind !== 'and') throw new Error('expected step conjunction')
    expectAtom(stepImplication.left.left, 'P', ['n'])
    expectAtom(stepImplication.left.right, 'S', ['n', 'm'])
    expectAtom(stepImplication.right, 'P', ['m'])
    expectAtom(predicateImplication.right, 'P', ['z'])
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

  it('applies standard precedence across negation, conjunction, disjunction, implication, and biconditional', () => {
    const formula = parseFormula('∀ A B C D : o. ¬A ∧ B ∨ C → D ↔ A')
    expect(formula.kind).toBe('quantifier')
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expect(formula.body.kind).toBe('iff')
    if (formula.body.kind !== 'iff') throw new Error('expected biconditional')
    expect(formula.body.left.kind).toBe('implies')
    if (formula.body.left.kind !== 'implies') throw new Error('expected implication')
    expect(formula.body.left.left.kind).toBe('or')
    if (formula.body.left.left.kind !== 'or') throw new Error('expected disjunction')
    expect(formula.body.left.left.left.kind).toBe('and')
    if (formula.body.left.left.left.kind !== 'and') throw new Error('expected conjunction')
    expect(formula.body.left.left.left.left.kind).toBe('not')
  })

  it('accepts ASCII quantifiers, implications, and Unicode conjunction', () => {
    expect(() => parseFormula('forall P : i -> o. exists x. P(x)')).not.toThrow()
    expect(() => parseFormula('∀ P : i => o. ∃ x. P(x) ∧ P(x)')).not.toThrow()
  })

  it('parses equality between same-signature bound variables', () => {
    const formula = parseFormula('∀ x y. x = y')
    expect(formula.kind).toBe('quantifier')
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expectEquality(formula.body, ['x', 'y'])
  })

  it('accepts lambda terms as proposition operands', () => {
    expect(parseFormula('forall P : i -> o. P(λx. x)').kind).toBe('quantifier')

    const formula = parseFormula('(\\x. x) = (\\y. y)')
    expect(formula.kind).toBe('equality')
    if (formula.kind !== 'equality') throw new Error('expected equality')
    const [left, right] = formula.operands
    expect(left.kind).toBe('term')
    expect(right.kind).toBe('term')
    if (left.kind !== 'term' || right.kind !== 'term') throw new Error('expected term operands')
    expect(left.parsed.term).toEqual(right.parsed.term)

    const application = parseFormula('forall P : i -> o. forall f x. P(f x)')
    expect(application.kind).toBe('quantifier')
    if (application.kind !== 'quantifier' || application.body.kind !== 'quantifier') {
      throw new Error('expected nested quantifiers')
    }
    expect(application.body.body.kind).toBe('atom')
    if (application.body.body.kind !== 'atom') throw new Error('expected atom')
    expect(application.body.body.args[0]?.kind).toBe('term')
  })

  it('requires every term free identifier to resolve to an enclosing individual binding', () => {
    expect(() => parseFormula('forall P : i -> o. P(λx. x missing)'))
      .toThrow(/unbound term identifier 'missing'/i)
    expect(() => parseFormula('forall P : i -> o. forall Q : i -> o. P(λx. x Q)'))
      .toThrow(/term identifier 'Q' must have signature i/i)
  })

  it('parses chained equality into one immutable operand list', () => {
    const formula = parseFormula('∀ x y z. x = y = z')
    expect(formula.kind).toBe('quantifier')
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expectEquality(formula.body, ['x', 'y', 'z'])
  })

  it('accepts equality at relation signatures and rejects mismatched signatures', () => {
    const formula = parseFormula('∀ P Q : i → o. P = Q')
    expect(formula.kind).toBe('quantifier')
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expectEquality(formula.body, ['P', 'Q'])

    expect(() => parseFormula('∀ P : i → o. ∀ x. P = x'))
      .toThrow(/equality operands must have the same signature/i)
  })

  it('rejects a signature mismatch anywhere in an equality chain', () => {
    expect(() => parseFormula('∀ P Q : i → o. ∀ x. P = Q = x'))
      .toThrow(/equality operands must have the same signature/i)
  })

  it('requires both equality operands to be bound variables', () => {
    expect(() => parseFormula('∀ x. x = missing'))
      .toThrow(/unbound equality operand 'missing'/i)
    expect(() => parseFormula('missing = missing'))
      .toThrow(/unbound equality operand 'missing'/i)
  })

  it('returns immutable syntax', () => {
    const formula = parseFormula(EXAMPLE_SOURCE)
    expect(Object.isFrozen(formula)).toBe(true)
    if (formula.kind !== 'quantifier') throw new Error('expected quantifier')
    expect(Object.isFrozen(formula.binders)).toBe(true)
    expect(Object.isFrozen(formula.binders[0]!)).toBe(true)
    if (formula.body.kind !== 'quantifier' || formula.body.body.kind !== 'implies') throw new Error('expected typed implication')
    const existentialZ = formula.body.body.left
    if (existentialZ.kind !== 'quantifier' || existentialZ.body.kind !== 'atom') throw new Error('expected existential atom')
    expect(Object.isFrozen(existentialZ.body.args)).toBe(true)
    expect(Object.isFrozen(existentialZ.body.span)).toBe(true)
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
