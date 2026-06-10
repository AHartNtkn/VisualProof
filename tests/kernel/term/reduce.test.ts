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

  it('decrements indices above the substituted variable', () => {
    // (\x. bvar(1)) a — body refers past the binder; after reduction it is bvar(0)
    expect(termEq(betaReduce(bvar(1), port('a')), bvar(0))).toBe(true)
  })

  it('drops the argument when the binder is unused (K behavior)', () => {
    expect(termEq(betaReduce(port('c'), app(port('y'), port('y'))), port('c'))).toBe(true)
  })
})
