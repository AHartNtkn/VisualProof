import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app, termEq } from '../../../src/kernel/term/term'
import { parseTerm, ParseError } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

const consts = new Set(['plus', 'one'])

describe('parseTerm', () => {
  it('parses identity with \\ for lambda', () => {
    expect(termEq(parseTerm('\\x. x', consts), lam(bvar(0)))).toBe(true)
  })

  it('parses Church two', () => {
    const expected = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(termEq(parseTerm('\\f. \\x. f (f x)', consts), expected)).toBe(true)
  })

  it('supports multi-binder sugar \\x y. e', () => {
    expect(termEq(parseTerm('\\f x. f x', consts), parseTerm('\\f. \\x. f x', consts))).toBe(true)
  })

  it('application is left-associative and binds tighter than lambda body', () => {
    expect(termEq(parseTerm('f a b', consts), app(app(port('f'), port('a')), port('b')))).toBe(true)
    expect(termEq(parseTerm('\\x. f x x', consts), lam(app(app(port('f'), bvar(0)), bvar(0))))).toBe(true)
  })

  it('resolves names: bound > const > port; inner binders shadow outer', () => {
    expect(termEq(parseTerm('plus one y', consts), app(app(cnst('plus'), cnst('one')), port('y')))).toBe(true)
    // bound name shadows a constant
    expect(termEq(parseTerm('\\plus. plus', consts), lam(bvar(0)))).toBe(true)
    // inner x shadows outer x
    expect(termEq(parseTerm('\\x. \\x. x', consts), lam(lam(bvar(0))))).toBe(true)
  })

  it('round-trips with the printer', () => {
    const src = '\\x0. \\x1. x0 (x0 x1)'
    expect(printTerm(parseTerm(src, consts))).toBe(src)
  })

  it('rejects empty input, unbalanced parens, and stray dots with positions', () => {
    expect(() => parseTerm('', consts)).toThrowError(ParseError)
    expect(() => parseTerm('(f a', consts)).toThrowError(/expected '\)'.*position 4/i)
    expect(() => parseTerm('f . a', consts)).toThrowError(/unexpected '\.'/i)
    expect(() => parseTerm('\\. x', consts)).toThrowError(/expected binder name/i)
  })
})
