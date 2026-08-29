import { application, bound, free, lambda, type Term } from './term'

export type ParsedTerm = {
  readonly term: Term
  readonly freeIdentifiers: readonly string[]
}

export class ParseError extends Error {
  constructor(message: string, readonly position: number) {
    super(`${message} at position ${position}`)
    this.name = 'ParseError'
  }
}

type Token =
  | { kind: 'lambda'; pos: number }
  | { kind: 'dot'; pos: number }
  | { kind: 'lparen'; pos: number }
  | { kind: 'rparen'; pos: number }
  | { kind: 'ident'; name: string; pos: number }

const IDENT_START = /[A-Za-z_]/
const IDENT_CONT = /[A-Za-z0-9_']/

function tokenize(source: string): Token[] {
  const tokens: Token[] = []
  let position = 0
  while (position < source.length) {
    const character = source[position]!
    if (/\s/.test(character)) {
      position++
      continue
    }
    if (character === '\\') {
      tokens.push({ kind: 'lambda', pos: position++ })
      continue
    }
    if (character === '.') {
      tokens.push({ kind: 'dot', pos: position++ })
      continue
    }
    if (character === '(') {
      tokens.push({ kind: 'lparen', pos: position++ })
      continue
    }
    if (character === ')') {
      tokens.push({ kind: 'rparen', pos: position++ })
      continue
    }
    if (IDENT_START.test(character)) {
      const start = position
      while (position < source.length && IDENT_CONT.test(source[position]!)) position++
      tokens.push({ kind: 'ident', name: source.slice(start, position), pos: start })
      continue
    }
    throw new ParseError(`unexpected character '${character}'`, position)
  }
  return tokens
}

/**
 * Parse text into a nameless term. Binder spellings are parser-local, and free
 * spellings are returned separately in first-occurrence slot order.
 */
export function parseTerm(source: string): ParsedTerm {
  const tokens = tokenize(source)
  if (tokens.length === 0) throw new ParseError('empty input', 0)
  const freeIdentifiers: string[] = []
  let position = 0

  const peek = (): Token | undefined => tokens[position]
  const endPosition = (): number => {
    const last = tokens[tokens.length - 1]!
    return last.kind === 'ident' ? last.pos + last.name.length : last.pos + 1
  }

  function parseAt(environment: readonly string[]): Term {
    const token = peek()
    if (token?.kind === 'lambda') {
      position++
      const names: string[] = []
      while (peek()?.kind === 'ident') {
        const binder = peek() as Extract<Token, { kind: 'ident' }>
        if (names.includes(binder.name)) {
          throw new ParseError(`duplicate binder name '${binder.name}' in binder group`, binder.pos)
        }
        names.push(binder.name)
        position++
      }
      if (names.length === 0) {
        throw new ParseError("expected binder name after '\\'", peek()?.pos ?? endPosition())
      }
      const dot = peek()
      if (dot?.kind !== 'dot') {
        throw new ParseError("expected '.' after binder names", dot?.pos ?? endPosition())
      }
      position++
      let body = parseAt([...environment, ...names])
      for (let index = 0; index < names.length; index++) body = lambda(body)
      return body
    }
    return parseApplication(environment)
  }

  function parseApplication(environment: readonly string[]): Term {
    let term = parseAtom(environment)
    for (;;) {
      const next = peek()
      if (next === undefined || next.kind === 'dot' || next.kind === 'rparen') break
      if (next.kind === 'lambda') {
        term = application(term, parseAt(environment))
        break
      }
      term = application(term, parseAtom(environment))
    }
    return term
  }

  function parseAtom(environment: readonly string[]): Term {
    const token = peek()
    if (token === undefined) throw new ParseError('unexpected end of input', endPosition())
    if (token.kind === 'ident') {
      position++
      const binder = environment.lastIndexOf(token.name)
      if (binder >= 0) return bound(environment.length - 1 - binder)
      let slot = freeIdentifiers.indexOf(token.name)
      if (slot < 0) {
        slot = freeIdentifiers.length
        freeIdentifiers.push(token.name)
      }
      return free(slot)
    }
    if (token.kind === 'lparen') {
      position++
      const inner = parseAt(environment)
      const close = peek()
      if (close?.kind !== 'rparen') {
        throw new ParseError("expected ')'", close?.pos ?? endPosition())
      }
      position++
      return inner
    }
    if (token.kind === 'dot') throw new ParseError("unexpected '.'", token.pos)
    throw new ParseError(`unexpected '${token.kind === 'rparen' ? ')' : '\\'}'`, token.pos)
  }

  const term = parseAt([])
  const leftover = peek()
  if (leftover !== undefined) {
    throw new ParseError(`unexpected '${tokenDisplay(leftover)}'`, leftover.pos)
  }
  return { term, freeIdentifiers }
}

function tokenDisplay(token: Token): string {
  switch (token.kind) {
    case 'ident': return token.name
    case 'dot': return '.'
    case 'lparen': return '('
    case 'rparen': return ')'
    case 'lambda': return '\\'
  }
}
