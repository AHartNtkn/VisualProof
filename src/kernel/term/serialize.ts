import { application, bound, free, lambda, type Term } from './term'

/** Stable injective ASCII serialization of nameless term structure. */
export function serializeTerm(term: Term): string {
  switch (term.kind) {
    case 'bound': return `B(${term.index})`
    case 'free': return `F(${term.slot})`
    case 'lambda': return `L(${serializeTerm(term.body)})`
    case 'application': return `A(${serializeTerm(term.fn)},${serializeTerm(term.argument)})`
  }
}

export function deserializeTerm(source: string): Term {
  const [term, rest] = parse(source, 0)
  if (rest !== source.length) {
    throw new Error(`malformed term serialization: trailing input at ${rest}`)
  }
  return term
}

function parse(source: string, position: number): [Term, number] {
  const fail = (message: string): never => {
    throw new Error(`malformed term serialization at ${position}: ${message}`)
  }
  const tag = source[position] ?? fail('unexpected end')
  if (tag === 'B' || tag === 'F') {
    if (source[position + 1] !== '(') fail(`expected '(' after ${tag}`)
    let end = position + 2
    while (end < source.length && source[end]! >= '0' && source[end]! <= '9') end++
    if (end === position + 2) fail(`expected digits inside ${tag}(...)`)
    if (source[end] !== ')') fail(`expected ')' closing ${tag}(...)`)
    const digits = source.slice(position + 2, end)
    const value = Number(digits)
    if (!Number.isSafeInteger(value)) fail(`${tag === 'B' ? 'bound index' : 'free slot'} ${digits} exceeds the safe integer range`)
    return [tag === 'B' ? bound(value) : free(value), end + 1]
  }
  if (tag === 'L') {
    if (source[position + 1] !== '(') fail("expected '(' after L")
    const [body, end] = parse(source, position + 2)
    if (source[end] !== ')') fail("expected ')' closing L(...)")
    return [lambda(body), end + 1]
  }
  if (tag === 'A') {
    if (source[position + 1] !== '(') fail("expected '(' after A")
    const [fn, separator] = parse(source, position + 2)
    if (source[separator] !== ',') fail("expected ',' inside A(...)")
    const [argument, end] = parse(source, separator + 1)
    if (source[end] !== ')') fail("expected ')' closing A(...)")
    return [application(fn, argument), end + 1]
  }
  return fail(`unexpected character '${tag}'`)
}
