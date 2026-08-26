import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

describe('term parser', () => {
  it('erases binder spelling and canonicalizes free identifiers by occurrence', () => {
    expect(parseTerm('\\x. x y').term).toEqual({
      kind: 'lambda',
      body: {
        kind: 'application',
        fn: { kind: 'bound', index: 0 },
        argument: { kind: 'free', slot: 0 },
      },
    })
    expect(parseTerm('\\z. z y').term).toEqual(parseTerm('\\x. x y').term)
    expect(parseTerm('\\x. x y').freeIdentifiers).toEqual(['y'])
  })

  it('parses nested binders, multi-binder sugar, and left-associated application', () => {
    expect(parseTerm('\\f x. f (f x)').term).toEqual({
      kind: 'lambda',
      body: {
        kind: 'lambda',
        body: {
          kind: 'application',
          fn: { kind: 'bound', index: 1 },
          argument: {
            kind: 'application',
            fn: { kind: 'bound', index: 1 },
            argument: { kind: 'bound', index: 0 },
          },
        },
      },
    })
    expect(parseTerm('f a b').term).toEqual({
      kind: 'application',
      fn: {
        kind: 'application',
        fn: { kind: 'free', slot: 0 },
        argument: { kind: 'free', slot: 1 },
      },
      argument: { kind: 'free', slot: 2 },
    })
    expect(parseTerm('f a f').freeIdentifiers).toEqual(['f', 'a'])
  })

  it('supports a lambda as the final application argument and inner shadowing', () => {
    expect(parseTerm('f \\x. x').term).toEqual(parseTerm('f (\\x. x)').term)
    expect(parseTerm('\\x. \\x. x').term).toEqual({
      kind: 'lambda',
      body: { kind: 'lambda', body: { kind: 'bound', index: 0 } },
    })
  })

  it('round-trips through the printer while keeping names at the boundary', () => {
    const parsed = parseTerm('\\x0. \\x1. x0 (x0 x1)')
    expect(printTerm(parsed.term, parsed.freeIdentifiers)).toBe('\\x0. \\x1. x0 (x0 x1)')
    const open = parseTerm('plus m (\\x. x)')
    expect(parseTerm(printTerm(open.term, open.freeIdentifiers)).term).toEqual(open.term)
  })

  it('rejects malformed syntax with source positions', () => {
    expect(() => parseTerm('')).toThrowError(/empty input.*position 0/i)
    expect(() => parseTerm('f 0 g')).toThrowError(/unexpected character '0'.*position 2/i)
    expect(() => parseTerm('(f a')).toThrowError(/expected '\)'.*position 4/i)
    expect(() => parseTerm('f . a')).toThrowError(/unexpected '\.'.*position 2/i)
    expect(() => parseTerm('\\. x')).toThrowError(/expected binder name/i)
    expect(() => parseTerm('\\x x. x')).toThrowError(/duplicate binder name 'x'/i)
  })
})
