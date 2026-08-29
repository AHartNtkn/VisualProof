import type { Sig } from '../kernel/diagram/sig'
import type { ParsedTerm } from '../kernel/term'

export type SourceSpan = { readonly start: number; readonly end: number }

export type FormulaBinder = {
  readonly name: string
  readonly sig: Sig
  readonly span: SourceSpan
}

export type FormulaUnicodeTokenKind =
  | 'forall'
  | 'exists'
  | 'not'
  | 'and'
  | 'or'
  | 'implies'
  | 'iff'
  | 'lambda'

export type FormulaUnicodeSymbol = {
  readonly symbol: string
  readonly label: string
  readonly token: FormulaUnicodeTokenKind
}

export const FORMULA_UNICODE_SYMBOLS = Object.freeze([
  { symbol: '∀', label: 'Universal quantifier', token: 'forall' },
  { symbol: '∃', label: 'Existential quantifier', token: 'exists' },
  { symbol: '¬', label: 'Negation', token: 'not' },
  { symbol: '∧', label: 'Conjunction', token: 'and' },
  { symbol: '∨', label: 'Disjunction', token: 'or' },
  { symbol: '→', label: 'Implication', token: 'implies' },
  { symbol: '⇒', label: 'Alternative implication', token: 'implies' },
  { symbol: '↔', label: 'Biconditional', token: 'iff' },
  { symbol: 'λ', label: 'Lambda abstraction', token: 'lambda' },
] as const satisfies readonly FormulaUnicodeSymbol[])

export type FormulaOperand =
  | { readonly kind: 'reference'; readonly name: string; readonly span: SourceSpan }
  | { readonly kind: 'term'; readonly parsed: ParsedTerm; readonly span: SourceSpan }

export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly FormulaOperand[]; readonly span: SourceSpan }
  | { readonly kind: 'equality'; readonly operands: readonly [FormulaOperand, FormulaOperand, ...FormulaOperand[]]; readonly span: SourceSpan }
  | { readonly kind: 'not'; readonly body: Formula; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'or'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'iff'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'quantifier'; readonly quantifier: 'exists' | 'forall'; readonly binders: readonly FormulaBinder[]; readonly body: Formula; readonly span: SourceSpan }

export class FormulaError extends Error {
  readonly offset: number

  constructor(source: string, offset: number, message: string) {
    const clampedOffset = Math.max(0, Math.min(offset, source.length))
    const before = source.slice(0, clampedOffset)
    const line = before.split('\n').length
    const lineStart = before.lastIndexOf('\n') + 1
    const column = clampedOffset - lineStart + 1
    super(`${message} at line ${line}, column ${column}`)
    this.name = 'FormulaError'
    this.offset = clampedOffset
  }
}
