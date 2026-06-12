import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app, termEq, freePorts, renameFreePorts, assertWellFormedTerm } from '../../../src/kernel/term/term'

describe('term constructors and equality', () => {
  it('structural equality is alpha-equality because binders are de Bruijn', () => {
    // \x. x  and  \y. y  are the same term: lam(bvar(0))
    const id1 = lam(bvar(0))
    const id2 = lam(bvar(0))
    expect(termEq(id1, id2), 'identical structure must be equal').toBe(true)
  })

  it('distinguishes structurally different terms', () => {
    expect(termEq(lam(bvar(0)), lam(lam(bvar(0))))).toBe(false)
    expect(termEq(port('y'), port('z'))).toBe(false)
    expect(termEq(cnst('plus'), port('plus'))).toBe(false)
    expect(termEq(app(port('f'), port('a')), app(port('a'), port('f')))).toBe(false)
  })

  it('rejects negative de Bruijn indices at construction', () => {
    expect(() => bvar(-1)).toThrowError(/negative/i)
  })

  it('rejects fractional de Bruijn indices at construction', () => {
    expect(() => bvar(0.5)).toThrowError(/fractional/i)
  })

  it('rejects unsafely large de Bruijn indices at construction', () => {
    expect(() => bvar(2 ** 53)).toThrowError(/safe integer/i)
  })

  it('rejects empty port and const names at construction', () => {
    expect(() => port('')).toThrowError(/non-empty/i)
    expect(() => cnst('')).toThrowError(/non-empty/i)
  })

  it('is reflexive on compound terms', () => {
    const t = app(cnst('plus'), port('m'))
    expect(termEq(t, t)).toBe(true)
  })
})

describe('freePorts', () => {
  it('returns ports in first-occurrence order (fn before arg, outside-in)', () => {
    // \x. y (z y x) — first occurrences: y, then z
    const t = lam(app(port('y'), app(app(port('z'), port('y')), bvar(0))))
    expect(freePorts(t)).toEqual(['y', 'z'])
  })

  it('returns empty list for closed terms', () => {
    const churchTwo = lam(lam(app(bvar(1), app(bvar(1), bvar(0)))))
    expect(freePorts(churchTwo)).toEqual([])
  })

  it('does not count constants as ports', () => {
    const t = app(cnst('plus'), port('m'))
    expect(freePorts(t)).toEqual(['m'])
  })
})

describe('renameFreePorts', () => {
  it('renames mapped ports and leaves unmapped ports unchanged', () => {
    const t = app(port('a'), port('keep'))
    const out = renameFreePorts(t, new Map([['a', 'x']]))
    expect(termEq(out, app(port('x'), port('keep')))).toBe(true)
  })

  it('is simultaneous: each leaf is looked up once by its ORIGINAL name', () => {
    // chained map {a→b, b→c}: 'a' must become 'b', NOT 'c'
    const t = app(port('a'), port('b'))
    const out = renameFreePorts(t, new Map([['a', 'b'], ['b', 'c']]))
    expect(termEq(out, app(port('b'), port('c')))).toBe(true)
  })

  it('exchanges ports under a swap map {a→b, b→a}', () => {
    const t = app(app(port('a'), port('b')), port('a'))
    const out = renameFreePorts(t, new Map([['a', 'b'], ['b', 'a']]))
    expect(termEq(out, app(app(port('b'), port('a')), port('b')))).toBe(true)
  })

  it('leaves bound variables and constants untouched, descending through lam and app', () => {
    const t = lam(app(app(bvar(0), cnst('plus')), port('a')))
    const out = renameFreePorts(t, new Map([['a', 'b'], ['plus', 'NOT-A-PORT']]))
    expect(termEq(out, lam(app(app(bvar(0), cnst('plus')), port('b'))))).toBe(true)
  })

  it('rejects an empty replacement name loudly', () => {
    expect(() => renameFreePorts(port('a'), new Map([['a', '']]))).toThrowError(/non-empty/)
  })
})

describe('assertWellFormedTerm', () => {
  it('accepts closed and open well-formed terms', () => {
    expect(() => assertWellFormedTerm(lam(bvar(0)))).not.toThrow()
    expect(() => assertWellFormedTerm(app(port('y'), cnst('plus')))).not.toThrow()
  })

  it('rejects unbound de Bruijn indices', () => {
    expect(() => assertWellFormedTerm({ kind: 'bvar', index: 0 })).toThrowError(/unbound de Bruijn index 0/)
    expect(() => assertWellFormedTerm(lam({ kind: 'bvar', index: 1 }))).toThrowError(/unbound de Bruijn index 1/)
  })

  it('rejects structural literals that bypass the smart constructors', () => {
    expect(() => assertWellFormedTerm({ kind: 'port', name: '' })).toThrowError(/non-empty/)
    expect(() => assertWellFormedTerm({ kind: 'const', id: '' })).toThrowError(/non-empty/)
    expect(() => assertWellFormedTerm({ kind: 'bvar', index: -1 })).toThrowError(/non-negative safe integer/)
  })
})
