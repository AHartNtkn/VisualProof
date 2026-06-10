import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { termEq } from '../../../src/kernel/term/term'
import { subtermAt, replaceSubtermAt, isBvarClosed, substPort, freshPortName } from '../../../src/kernel/term/path'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('subtermAt / replaceSubtermAt', () => {
  it('navigates body/fn/arg and round-trips replacement', () => {
    const t = p('\\x. (\\y. y) x')
    expect(printTerm(subtermAt(t, ['body', 'fn']))).toBe(printTerm(p('\\y. y')))
    const swapped = replaceSubtermAt(t, ['body', 'fn'], p('\\y. z'))
    expect(printTerm(subtermAt(swapped, ['body', 'fn']))).toBe(printTerm(p('\\y. z')))
    expect(termEq(replaceSubtermAt(swapped, ['body', 'fn'], p('\\y. y')), t)).toBe(true)
  })

  it('the empty path is the whole term', () => {
    const t = p('x y')
    expect(termEq(subtermAt(t, []), t)).toBe(true)
    expect(termEq(replaceSubtermAt(t, [], p('z')), p('z'))).toBe(true)
  })

  it('rejects invalid paths by position and kind', () => {
    expect(() => subtermAt(p('x'), ['body'])).toThrowError(/invalid path segment 'body' at position 0 into 'port'/)
    expect(() => replaceSubtermAt(p('\\x. x'), ['fn'], p('y'))).toThrowError(/invalid path segment 'fn' into 'lam'/)
  })
})

describe('isBvarClosed', () => {
  it('accepts internally bound bvars and rejects escaping ones', () => {
    expect(isBvarClosed(p('\\x. x'))).toBe(true)
    expect(isBvarClosed(p('y'))).toBe(true)
    // the subterm `x` of `\x. x` escapes: bvar 0 at depth 0
    expect(isBvarClosed(subtermAt(p('\\x. x'), ['body']))).toBe(false)
    expect(isBvarClosed(subtermAt(p('\\x. \\y. x y'), ['body', 'body']))).toBe(false)
  })
})

describe('substPort', () => {
  it('replaces every occurrence, including under binders, without shifting', () => {
    const t = p('\\x. q (x q)')
    const out = substPort(t, 'q', p('\\y. y'))
    expect(printTerm(out)).toBe(printTerm(p('\\x. (\\y. y) (x (\\y. y))')))
  })

  it('leaves other ports and bvars alone', () => {
    const t = p('\\x. r x')
    expect(termEq(substPort(t, 'q', p('z')), t)).toBe(true)
  })

  it('rejects a replacement that is not bvar-closed', () => {
    const escaping = subtermAt(p('\\x. x'), ['body'])
    expect(() => substPort(p('q'), 'q', escaping)).toThrowError(/replacement must be bvar-closed/)
  })
})

describe('freshPortName', () => {
  it('returns the base when free, else suffixes deterministically', () => {
    expect(freshPortName(new Set(), 'x')).toBe('x')
    expect(freshPortName(new Set(['x']), 'x')).toBe('x_0')
    expect(freshPortName(new Set(['x', 'x_0']), 'x')).toBe('x_1')
  })
})
