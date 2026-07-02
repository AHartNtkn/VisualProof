import type { Term } from './term'
import { bvar, port, lam, app } from './term'

/**
 * Stable, injective, ASCII serialization. De Bruijn makes this canonical for
 * alpha-equivalence by construction: equal serializations iff termEq. Names are
 * JSON-escaped so no name can forge structure. This string is the term-level
 * content key used by diagram canonicalization and fingerprints (Plan 2).
 */
export function serializeTerm(t: Term): string {
  switch (t.kind) {
    case 'bvar': return `#${t.index}`
    case 'port': return `P(${JSON.stringify(t.name)})`
    case 'lam': return `L(${serializeTerm(t.body)})`
    case 'app': return `A(${serializeTerm(t.fn)},${serializeTerm(t.arg)})`
  }
}

export function deserializeTerm(s: string): Term {
  const [term, rest] = parse(s, 0)
  if (rest !== s.length) throw new Error(`malformed term serialization: trailing input at ${rest}`)
  return term
}

function parse(s: string, i: number): [Term, number] {
  const fail = (msg: string): never => { throw new Error(`malformed term serialization at ${i}: ${msg}`) }
  const c = s[i] ?? fail('unexpected end')
  if (c === '#') {
    // Leading zeros are accepted; serializeTerm never emits them, so
    // non-canonical inputs decode to the unique canonical term.
    let j = i + 1
    while (j < s.length && s[j]! >= '0' && s[j]! <= '9') j++
    if (j === i + 1) fail('expected digits after #')
    const digits = s.slice(i + 1, j)
    const value = Number(digits)
    if (!Number.isSafeInteger(value)) fail(`bvar index ${digits} exceeds the safe integer range`)
    return [bvar(value), j]
  }
  if (c === 'P') {
    if (s[i + 1] !== '(') fail("expected '(' after P")
    const [str, j] = parseJsonString(s, i + 2)
    if (s[j] !== ')') fail("expected ')' closing P(...)")
    return [port(str), j + 1]
  }
  if (c === 'L') {
    if (s[i + 1] !== '(') fail("expected '(' after L")
    const [body, j] = parse(s, i + 2)
    if (s[j] !== ')') fail("expected ')' closing L(...)")
    return [lam(body), j + 1]
  }
  if (c === 'A') {
    if (s[i + 1] !== '(') fail("expected '(' after A")
    const [fn, j] = parse(s, i + 2)
    if (s[j] !== ',') fail("expected ',' inside A(...)")
    const [arg, k] = parse(s, j + 1)
    if (s[k] !== ')') fail("expected ')' closing A(...)")
    return [app(fn, arg), k + 1]
  }
  return fail(`unexpected character '${c}'`)
}

function parseJsonString(s: string, i: number): [string, number] {
  if (s[i] !== '"') throw new Error(`malformed term serialization at ${i}: expected '"'`)
  let j = i + 1
  while (j < s.length) {
    if (s[j] === '\\') { j += 2; continue }
    if (s[j] === '"') {
      try {
        return [JSON.parse(s.slice(i, j + 1)) as string, j + 1]
      } catch (e) {
        throw new Error(`malformed term serialization at ${i}: invalid JSON string (${e instanceof Error ? e.message : String(e)})`)
      }
    }
    j++
  }
  throw new Error(`malformed term serialization at ${i}: unterminated string`)
}
