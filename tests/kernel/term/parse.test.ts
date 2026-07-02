import { describe, it, expect } from 'vitest'
import { bvar, port, lam, app, termEq } from '../../../src/kernel/term/term'
import { parseTerm, ParseError } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

describe('parseTerm', () => {
  it('parses identity with \\ for lambda', () => {
    expect(termEq(parseTerm('\\x. x'), lam(bvar(0)))).toBe(true)
  })

  it('parses Church two', () => {
    const expected = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(termEq(parseTerm('\\f. \\x. f (f x)'), expected)).toBe(true)
  })

  it('supports multi-binder sugar \\x y. e', () => {
    expect(termEq(parseTerm('\\f x. f x'), parseTerm('\\f. \\x. f x'))).toBe(true)
  })

  it('application is left-associative and binds tighter than lambda body', () => {
    expect(termEq(parseTerm('f a b'), app(app(port('f'), port('a')), port('b')))).toBe(true)
    expect(termEq(parseTerm('\\x. f x x'), lam(app(app(port('f'), bvar(0)), bvar(0))))).toBe(true)
  })

  it('treats a lambda in argument position as the final argument extending to the end', () => {
    expect(termEq(parseTerm('f \\x. x'), app(port('f'), lam(bvar(0))))).toBe(true)
    expect(termEq(parseTerm('f g \\x. x'), app(app(port('f'), port('g')), lam(bvar(0))))).toBe(true)
    expect(termEq(parseTerm('\\x. f \\y. y'), lam(app(port('f'), lam(bvar(0)))))).toBe(true)
  })

  it('rejects duplicate binder names within one binder group', () => {
    expect(() => parseTerm('\\x x. x')).toThrowError(/duplicate binder name 'x'/i)
    // shadowing across nested lambdas remains legal (covered elsewhere): \x. \x. x
  })

  it('rejects unexpected characters with positions', () => {
    expect(() => parseTerm('f α g')).toThrowError(ParseError)
    expect(() => parseTerm('f 0 g')).toThrowError(/unexpected character '0'/i)
  })

  it('resolves names: bound > port; inner binders shadow outer', () => {
    // every free identifier is a port (there is no constant namespace)
    expect(termEq(parseTerm('plus one y'), app(app(port('plus'), port('one')), port('y')))).toBe(true)
    // a bound name resolves to its de Bruijn index, shadowing a free port
    expect(termEq(parseTerm('\\plus. plus'), lam(bvar(0)))).toBe(true)
    // inner x shadows outer x
    expect(termEq(parseTerm('\\x. \\x. x'), lam(lam(bvar(0))))).toBe(true)
  })

  it('round-trips with the printer', () => {
    const src = '\\x0. \\x1. x0 (x0 x1)'
    expect(printTerm(parseTerm(src))).toBe(src)
    const withNames = 'plus m (\\x0. x0)'
    expect(printTerm(parseTerm(withNames))).toBe(withNames)
  })

  it('rejects empty input, unbalanced parens, and stray dots with positions', () => {
    expect(() => parseTerm('')).toThrowError(ParseError)
    expect(() => parseTerm('(f a')).toThrowError(/expected '\)'.*position 4/i)
    expect(() => parseTerm('f . a')).toThrowError(/unexpected '\.'/i)
    expect(() => parseTerm('\\. x')).toThrowError(/expected binder name/i)
  })
})
