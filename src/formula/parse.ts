import { IOTA, relSig, sigEquals, type Sig } from '../kernel/diagram/sig'
import { FormulaError, type Formula, type FormulaBinder, type SourceSpan } from './syntax'

type TokenKind = 'identifier' | 'forall' | 'exists' | 'implies' | 'and' | '(' | ')' | ',' | ':' | '.' | '=' | 'eof'

type Token = { readonly kind: TokenKind; readonly text: string; readonly start: number; readonly end: number }

type TypeExpression =
  | { readonly kind: 'base'; readonly name: 'i' | 'o'; readonly span: SourceSpan }
  | { readonly kind: 'arrow'; readonly domain: TypeExpression; readonly codomain: TypeExpression; readonly span: SourceSpan }

function tokenize(source: string): readonly Token[] {
  const tokens: Token[] = []
  let index = 0

  while (index < source.length) {
    const start = index
    const character = source[index]!
    if (/\s/u.test(character)) {
      index += 1
      continue
    }

    if (/[A-Za-z_]/u.test(character)) {
      index += 1
      while (index < source.length && /[A-Za-z0-9_]/u.test(source[index]!)) index += 1
      const text = source.slice(start, index)
      tokens.push({ kind: text === 'forall' ? 'forall' : text === 'exists' ? 'exists' : 'identifier', text, start, end: index })
      continue
    }

    const pair = source.slice(index, index + 2)
    if (pair === '->' || pair === '=>') {
      index += 2
      tokens.push({ kind: 'implies', text: pair, start, end: index })
      continue
    }

    const oneCharacterTokens: Readonly<Record<string, TokenKind>> = {
      '∀': 'forall',
      '∃': 'exists',
      '→': 'implies',
      '⇒': 'implies',
      '&': 'and',
      '∧': 'and',
      '(': '(',
      ')': ')',
      ',': ',',
      ':': ':',
      '.': '.',
      '=': '=',
    }
    const kind = oneCharacterTokens[character]
    if (kind !== undefined) {
      index += 1
      tokens.push({ kind, text: character, start, end: index })
      continue
    }

    throw new FormulaError(source, start, `unexpected character '${character}'`)
  }

  tokens.push({ kind: 'eof', text: '', start: source.length, end: source.length })
  return tokens
}

function frozenSpan(start: number, end: number): SourceSpan {
  return Object.freeze({ start, end })
}

function frozenAtom(name: string, args: readonly string[], start: number, end: number): Formula {
  return Object.freeze({ kind: 'atom', name, args: Object.freeze([...args]), span: frozenSpan(start, end) })
}

function frozenEquality(left: string, right: string, start: number, end: number): Formula {
  return Object.freeze({ kind: 'equality', left, right, span: frozenSpan(start, end) })
}

function frozenBinary(kind: 'and' | 'implies', left: Formula, right: Formula): Formula {
  return Object.freeze({ kind, left, right, span: frozenSpan(left.span.start, right.span.end) })
}

function frozenQuantifier(
  quantifier: 'exists' | 'forall',
  binders: readonly FormulaBinder[],
  start: number,
  body: Formula,
): Formula {
  return Object.freeze({
    kind: 'quantifier',
    quantifier,
    binders: Object.freeze([...binders]),
    body,
    span: frozenSpan(start, body.span.end),
  })
}

/** Parse, type-check, and lexically validate a formula source string. */
export function parseFormula(source: string): Formula {
  const tokens = tokenize(source)
  let current = 0

  function peek(): Token {
    return tokens[current]!
  }

  function take(): Token {
    const token = peek()
    current += 1
    return token
  }

  function expect(kind: TokenKind, description: string): Token {
    const token = peek()
    if (token.kind !== kind) throw new FormulaError(source, token.start, `expected ${description}`)
    return take()
  }

  function parseImplication(): Formula {
    const left = parseConjunction()
    if (peek().kind !== 'implies') return left
    take()
    return frozenBinary('implies', left, parseImplication())
  }

  function parseConjunction(): Formula {
    let formula = parsePrimary()
    while (peek().kind === 'and') {
      take()
      formula = frozenBinary('and', formula, parsePrimary())
    }
    return formula
  }

  function parsePrimary(): Formula {
    const token = peek()
    if (token.kind === 'forall' || token.kind === 'exists') return parseQuantifier()
    if (token.kind === '(') {
      take()
      const formula = parseImplication()
      expect(')', "')'")
      return formula
    }
    if (token.kind !== 'identifier') throw new FormulaError(source, token.start, 'expected a formula')

    const head = take()
    if (peek().kind === '=') {
      take()
      const right = expect('identifier', 'an equality operand')
      return frozenEquality(head.text, right.text, head.start, right.end)
    }
    const args: string[] = []
    let end = head.end
    if (peek().kind === '(') {
      take()
      if (peek().kind !== ')') {
        do {
          const argument = expect('identifier', 'an argument name')
          args.push(argument.text)
          if (peek().kind !== ',') break
          take()
        } while (true)
      }
      end = expect(')', "')'").end
    }
    return frozenAtom(head.text, args, head.start, end)
  }

  function parseQuantifier(): Formula {
    const quantifierToken = take()
    const quantifier: 'exists' | 'forall' = quantifierToken.kind === 'forall' ? 'forall' : 'exists'
    const binders: FormulaBinder[] = []
    const names = new Set<string>()

    do {
      const name = expect('identifier', 'a binder name')
      if (names.has(name.text)) throw new FormulaError(source, name.start, `duplicate binder '${name.text}'`)
      names.add(name.text)
      binders.push(Object.freeze({ name: name.text, sig: IOTA, span: frozenSpan(name.start, name.end) }))
    } while (peek().kind === 'identifier')

    if (peek().kind === ':') {
      take()
      const signature = signatureOf(parseType())
      for (let index = 0; index < binders.length; index += 1) {
        const binder = binders[index]!
        binders[index] = Object.freeze({ name: binder.name, sig: signature, span: binder.span })
      }
    }

    expect('.', "'.' after quantifier binders")
    const body = parseImplication()
    return frozenQuantifier(quantifier, binders, quantifierToken.start, body)
  }

  function parseType(): TypeExpression {
    const token = expect('identifier', 'a type')
    if (token.text !== 'i' && token.text !== 'o') {
      throw new FormulaError(source, token.start, `unknown type '${token.text}'`)
    }
    const base: TypeExpression = { kind: 'base', name: token.text, span: frozenSpan(token.start, token.end) }
    if (peek().kind !== 'implies') return base
    take()
    const codomain = parseType()
    return { kind: 'arrow', domain: base, codomain, span: frozenSpan(base.span.start, codomain.span.end) }
  }

  function signatureOf(type: TypeExpression): Sig {
    if (type.kind === 'base') return type.name === 'i' ? IOTA : relSig([])

    const domains: Sig[] = []
    let cursor: TypeExpression = type
    while (cursor.kind === 'arrow') {
      domains.push(signatureOf(cursor.domain))
      cursor = cursor.codomain
    }
    if (cursor.name !== 'o') {
      throw new FormulaError(source, cursor.span.start, 'relation types must end in o')
    }
    return relSig(domains)
  }

  function validate(formula: Formula, environment: ReadonlyMap<string, Sig>): void {
    switch (formula.kind) {
      case 'and':
      case 'implies':
        validate(formula.left, environment)
        validate(formula.right, environment)
        return
      case 'quantifier': {
        const nested = new Map(environment)
        for (const binder of formula.binders) nested.set(binder.name, binder.sig)
        validate(formula.body, nested)
        return
      }
      case 'equality': {
        const left = environment.get(formula.left)
        if (left === undefined) {
          throw new FormulaError(source, formula.span.start, `unbound equality operand '${formula.left}'`)
        }
        const right = environment.get(formula.right)
        if (right === undefined) {
          throw new FormulaError(source, formula.span.start, `unbound equality operand '${formula.right}'`)
        }
        if (!sigEquals(left, right)) {
          throw new FormulaError(source, formula.span.start, 'equality operands must have the same signature')
        }
        return
      }
      case 'atom': {
        const head = environment.get(formula.name)
        if (head === undefined) throw new FormulaError(source, formula.span.start, `unbound application name '${formula.name}'`)
        if (head.kind !== 'rel') throw new FormulaError(source, formula.span.start, `application name '${formula.name}' is not a relation`)
        if (head.args.length !== formula.args.length) {
          throw new FormulaError(source, formula.span.start, `application '${formula.name}' has arity ${formula.args.length}, expected ${head.args.length}`)
        }
        for (let index = 0; index < formula.args.length; index += 1) {
          const argumentName = formula.args[index]!
          const argument = environment.get(argumentName)
          if (argument === undefined) throw new FormulaError(source, formula.span.start, `unbound argument name '${argumentName}'`)
          if (!sigEquals(argument, head.args[index]!)) {
            throw new FormulaError(source, formula.span.start, `argument '${argumentName}' does not match the expected signature`)
          }
        }
      }
    }
  }

  const formula = parseImplication()
  const trailing = peek()
  if (trailing.kind !== 'eof') throw new FormulaError(source, trailing.start, `unexpected token '${trailing.text}'`)
  validate(formula, new Map())
  return formula
}
