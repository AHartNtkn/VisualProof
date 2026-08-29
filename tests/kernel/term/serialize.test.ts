import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { deserializeTerm, serializeTerm } from '../../../src/kernel/term/serialize'
import { free, termEq } from '../../../src/kernel/term/term'

const p = (source: string) => parseTerm(source).term

describe('term serialization', () => {
  it('round-trips every term shape and is injective on distinct structures', () => {
    const terms = ['\\x. x', '\\f. \\x. f (f x)', 'plus m m', '\\x. y (y x)', 'f (\\x. x) b'].map(p)
    for (const term of terms) expect(termEq(deserializeTerm(serializeTerm(term)), term)).toBe(true)
    expect(new Set(terms.map(serializeTerm)).size).toBe(terms.length)
  })

  it('serializes canonical free slots rather than parser spellings', () => {
    expect(serializeTerm(p('alpha alpha'))).toBe(serializeTerm(p('beta beta')))
    expect(serializeTerm(free(0))).not.toBe(serializeTerm(free(1)))
  })

  it('rejects malformed and unsafe numeric input', () => {
    for (const source of ['L(', 'garbage', 'F(0)x', 'B(9007199254740993)']) {
      expect(() => deserializeTerm(source)).toThrowError(/malformed/i)
    }
  })
})
