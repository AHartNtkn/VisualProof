import { describe, it, expect } from 'vitest'
import { bvar, port, cnst, lam, app, termEq, freePorts } from '../../../src/kernel/term/term'

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
