import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app } from '../../../src/kernel/term/term'
import { printTerm } from '../../../src/kernel/term/print'

describe('printTerm', () => {
  it('prints identity', () => {
    expect(printTerm(lam(bvar(0)))).toBe('\\x0. x0')
  })

  it('prints Church two with nested binders named outside-in', () => {
    const churchTwo = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(printTerm(churchTwo)).toBe('\\x0. \\x1. x0 (x0 x1)')
  })

  it('prints application left-associatively without redundant parens', () => {
    const t = app(app(port('f'), port('a')), port('b'))
    expect(printTerm(t)).toBe('f a b')
  })

  it('parenthesizes argument applications and lambda operands', () => {
    expect(printTerm(app(port('f'), app(port('g'), port('a'))))).toBe('f (g a)')
    expect(printTerm(app(lam(bvar(0)), port('a')))).toBe('(\\x0. x0) a')
    expect(printTerm(app(port('f'), lam(bvar(0))))).toBe('f (\\x0. x0)')
  })

  it('prints ports and constants by name', () => {
    expect(printTerm(app(cnst('plus'), port('m')))).toBe('plus m')
  })

  it('avoids capture-looking collisions with port names by prefixing underscores', () => {
    // port literally named x0 — binder must not print as x0
    const t = lam(app(bvar(0), port('x0')))
    expect(printTerm(t)).toBe('\\_x0. _x0 x0')
  })

  it('throws on unbound de Bruijn index', () => {
    expect(() => printTerm(bvar(0))).toThrowError(/unbound de Bruijn index 0/)
  })
})
