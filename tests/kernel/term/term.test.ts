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
