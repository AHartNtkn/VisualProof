import type { Sig } from '../kernel/diagram/sig'

export type SourceSpan = { readonly start: number; readonly end: number }

export type FormulaBinder = {
  readonly name: string
  readonly sig: Sig
  readonly span: SourceSpan
}

export type Formula =
  | { readonly kind: 'atom'; readonly name: string; readonly args: readonly string[]; readonly span: SourceSpan }
  | { readonly kind: 'and'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
  | { readonly kind: 'implies'; readonly left: Formula; readonly right: Formula; readonly span: SourceSpan }
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
