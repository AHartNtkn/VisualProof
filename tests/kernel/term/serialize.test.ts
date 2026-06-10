import { describe, it, expect } from 'vitest'
import { termEq } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { serializeTerm, deserializeTerm } from '../../../src/kernel/term/serialize'

const consts = new Set(['plus'])
const p = (s: string) => parseTerm(s, consts)

describe('serializeTerm', () => {
  it('round-trips every term shape', () => {
    for (const src of ['\\x. x', '\\f. \\x. f (f x)', 'plus m m', '\\x. y (y x)', 'f (\\x. x) b']) {
      const t = p(src)
      const back = deserializeTerm(serializeTerm(t))
      expect(termEq(t, back), `round-trip failed for ${src}`).toBe(true)
    }
  })

  it('is injective on distinct terms (serialization is the content key)', () => {
    const a = serializeTerm(p('\\x. x x'))
    const b = serializeTerm(p('\\x. x'))
    const c = serializeTerm(p('plus'))
    const d = serializeTerm(p('plus2 v'))
    expect(new Set([a, b, c, d]).size).toBe(4)
  })

  it('escapes names safely: a port named with quotes or parens cannot forge structure', () => {
    const tricky = { kind: 'port' as const, name: '"),A(' }
    const back = deserializeTerm(serializeTerm(tricky))
    expect(termEq(tricky, back)).toBe(true)
  })

  it('rejects malformed input loudly', () => {
    expect(() => deserializeTerm('L(')).toThrowError(/malformed/i)
    expect(() => deserializeTerm('garbage')).toThrowError(/malformed/i)
    expect(() => deserializeTerm('P("a")x')).toThrowError(/malformed/i)
  })
})
