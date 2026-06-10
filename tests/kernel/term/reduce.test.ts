import { describe, it, expect } from 'vitest'
import { bvar, port, lam, app, termEq } from '../../../src/kernel/term/term'
import { shift, betaReduce } from '../../../src/kernel/term/reduce'

describe('shift', () => {
  it('shifts free indices at or above the cutoff', () => {
    // under one binder, index 0 is bound (below cutoff 1), index 1 is free
    const t = lam(app(bvar(0), bvar(1)))
    expect(termEq(shift(1, 0, t), lam(app(bvar(0), bvar(2))))).toBe(true)
  })

  it('leaves ports and constants untouched', () => {
    const t = app(port('y'), bvar(0))
    expect(termEq(shift(2, 0, t), app(port('y'), bvar(2)))).toBe(true)
  })

  it('throws when negative d produces a negative index', () => {
    expect(() => shift(-1, 0, bvar(0))).toThrow(/negative index/)
    expect(() => shift(-2, 0, bvar(1))).toThrow(/negative index/)
  })

  it('leaves indices below the cutoff unchanged', () => {
    // shift(1, 2, ...) must not touch bvar(0) or bvar(1)
    const t = app(bvar(0), app(bvar(1), bvar(2)))
    expect(termEq(shift(1, 2, t), app(bvar(0), app(bvar(1), bvar(3))))).toBe(true)
  })
})

describe('betaReduce', () => {
  it('substitutes the argument for the bound variable', () => {
    // (\x. x x) y  →  y y
    expect(termEq(betaReduce(app(bvar(0), bvar(0)), port('y')), app(port('y'), port('y')))).toBe(true)
  })

  it('avoids capture: argument indices shift under inner binders', () => {
    // (\x. \y. x) z  where z is bvar(0) in the surrounding context
    // body = \. bvar(1); arg = bvar(0)  →  \. bvar(1)  (arg shifted under the binder)
    const body = lam(bvar(1))
    const arg = bvar(0)
    expect(termEq(betaReduce(body, arg), lam(bvar(1)))).toBe(true)
  })

  it('correctly shifts arg with multiple free bvars under nested binders', () => {
    // (\x. \y. x) (app(bvar(0), bvar(1)))
    // body = lam(bvar(1)), arg = app(bvar(0), bvar(1))
    // result = lam(app(bvar(1), bvar(2)))  -- under \y, bvar(0)→bvar(1), bvar(1)→bvar(2)
    const result = betaReduce(lam(bvar(1)), app(bvar(0), bvar(1)))
    expect(termEq(result, lam(app(bvar(1), bvar(2))))).toBe(true)
  })

  it('decrements indices above the substituted variable', () => {
    // (\x. bvar(1)) a — body refers past the binder; after reduction it is bvar(0)
    expect(termEq(betaReduce(bvar(1), port('a')), bvar(0))).toBe(true)
  })

  it('drops the argument when the binder is unused (K behavior)', () => {
    expect(termEq(betaReduce(port('c'), app(port('y'), port('y'))), port('c'))).toBe(true)
  })
})
