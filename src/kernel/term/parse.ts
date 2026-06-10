import type { Term } from './term'
import { bvar, port, cnst, lam, app } from './term'

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

function tokenize(src: string): Token[] {
  const out: Token[] = []
  let i = 0
  while (i < src.length) {
    const c = src[i]!
    if (c === ' ' || c === '\t' || c === '\n' || c === '\r') { i++; continue }
    if (c === '\\') { out.push({ kind: 'lambda', pos: i }); i++; continue }
    if (c === '.') { out.push({ kind: 'dot', pos: i }); i++; continue }
    if (c === '(') { out.push({ kind: 'lparen', pos: i }); i++; continue }
    if (c === ')') { out.push({ kind: 'rparen', pos: i }); i++; continue }
    if (IDENT_START.test(c)) {
      const start = i
      while (i < src.length && IDENT_CONT.test(src[i]!)) i++
      out.push({ kind: 'ident', name: src.slice(start, i), pos: start })
      continue
    }
    throw new ParseError(`unexpected character '${c}'`, i)
  }
  return out
}

/**
 * Grammar:
 *   term   := lambda | appSeq
 *   lambda := '\' ident+ '.' term
 *   appSeq := atom atom*            (left-associative)
 *   atom   := ident | '(' term ')'
 * Name resolution: innermost binder first, then constants, then port.
 */
export function parseTerm(src: string, constIds: ReadonlySet<string>): Term {
  const tokens = tokenize(src)
  if (tokens.length === 0) throw new ParseError('empty input', 0)
  let i = 0

  const peek = (): Token | undefined => tokens[i]
  const endPos = (): number => {
    const last = tokens[tokens.length - 1]!
    return last.kind === 'ident' ? last.pos + last.name.length : last.pos + 1
  }

  function parseTermAt(env: string[]): Term {
    const t = peek()
    if (t !== undefined && t.kind === 'lambda') {
      i++
      const names: string[] = []
      for (;;) {
        const tok = peek()
        if (tok === undefined || tok.kind !== 'ident') break
        if (names.includes(tok.name)) {
          throw new ParseError(`duplicate binder name '${tok.name}' in binder group`, tok.pos)
        }
        names.push(tok.name)
        i++
      }
      if (names.length === 0) {
        throw new ParseError("expected binder name after '\\'", peek()?.pos ?? endPos())
      }
      const dot = peek()
      if (dot === undefined || dot.kind !== 'dot') {
        throw new ParseError("expected '.' after binder names", dot?.pos ?? endPos())
      }
      i++
      let body = parseTermAt([...env, ...names])
      for (let k = 0; k < names.length; k++) body = lam(body)
      return body
    }
    return parseAppSeq(env)
  }

  function parseAppSeq(env: string[]): Term {
    let t = parseAtom(env)
    for (;;) {
      const nxt = peek()
      if (nxt === undefined || nxt.kind === 'dot' || nxt.kind === 'rparen') break
      if (nxt.kind === 'lambda') {
        // '\' in argument position: standard λ-calculus convention (as in Haskell/ML) —
        // the lambda is the final argument and its body extends to the end of the expression.
        t = app(t, parseTermAt(env))
        break
      }
      t = app(t, parseAtom(env))
    }
    return t
  }

  function parseAtom(env: string[]): Term {
    const t = peek()
    if (t === undefined) throw new ParseError('unexpected end of input', endPos())
    if (t.kind === 'ident') {
      i++
      const idx = env.lastIndexOf(t.name)
      if (idx >= 0) return bvar(env.length - 1 - idx)
      if (constIds.has(t.name)) return cnst(t.name)
      return port(t.name)
    }
    if (t.kind === 'lparen') {
      i++
      const inner = parseTermAt(env)
      const close = peek()
      if (close === undefined || close.kind !== 'rparen') {
        throw new ParseError("expected ')'", close?.pos ?? endPos())
      }
      i++
      return inner
    }
    if (t.kind === 'dot') throw new ParseError("unexpected '.'", t.pos)
    throw new ParseError(`unexpected '${t.kind === 'rparen' ? ')' : '\\'}'`, t.pos)
  }

  const result = parseTermAt([])
  const leftover = peek()
  if (leftover !== undefined) {
    throw new ParseError(`unexpected '${tokenDisplay(leftover)}'`, leftover.pos)
  }
  return result
}

function tokenDisplay(t: Token): string {
  switch (t.kind) {
    case 'ident': return t.name
    case 'dot': return '.'
    case 'lparen': return '('
    case 'rparen': return ')'
    case 'lambda': return '\\'
  }
}
