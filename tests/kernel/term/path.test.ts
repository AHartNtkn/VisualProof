import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { isBoundClosed, replaceSubtermAt, substFree, subtermAt } from '../../../src/kernel/term/path'
import { termEq } from '../../../src/kernel/term/term'

const p = (source: string) => parseTerm(source).term

describe('term paths and free-slot substitution', () => {
  it('navigates body/fn/argument and round-trips replacement', () => {
    const term = p('\\x. (\\y. y) x')
    expect(termEq(subtermAt(term, ['body', 'fn']), p('\\y. y'))).toBe(true)
    const swapped = replaceSubtermAt(term, ['body', 'fn'], p('\\y. z'))
    expect(termEq(replaceSubtermAt(swapped, ['body', 'fn'], p('\\y. y')), term)).toBe(true)
    expect(termEq(replaceSubtermAt(term, [], p('z')), p('z'))).toBe(true)
  })

  it('rejects a path/term mismatch with position and kind', () => {
    expect(() => subtermAt(p('x'), ['body'])).toThrowError(/position 0.*free/i)
    expect(() => replaceSubtermAt(p('\\x. x'), ['fn'], p('y'))).toThrowError(/'fn'.*lambda/i)
  })

  it('detects escaping bound indices', () => {
    expect(isBoundClosed(p('\\x. x'))).toBe(true)
    expect(isBoundClosed(p('y'))).toBe(true)
    expect(isBoundClosed(subtermAt(p('\\x. x'), ['body']))).toBe(false)
    expect(isBoundClosed(subtermAt(p('\\x. \\y. x y'), ['body', 'body']))).toBe(false)
  })

  it('substitutes a numeric free slot under binders without capture', () => {
    const term = p('\\x. q (x q)')
    expect(termEq(substFree(term, 0, p('\\y. y')), p('\\x. (\\y. y) (x (\\y. y))'))).toBe(true)
    expect(termEq(substFree(p('\\x. r x'), 1, p('z')), p('\\x. r x'))).toBe(true)
    const escaping = subtermAt(p('\\x. x'), ['body'])
    expect(() => substFree(p('q'), 0, escaping)).toThrowError(/replacement must be bound-closed/i)
  })
})
