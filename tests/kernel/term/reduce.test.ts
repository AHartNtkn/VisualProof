import { describe, expect, it } from 'vitest'
import { application, bound, free, lambda, termEq } from '../../../src/kernel/term/term'
import { betaReduce, shift } from '../../../src/kernel/term/reduce'

describe('shift', () => {
  it('shifts bound indices at or above the cutoff through nested binders', () => {
    const term = lambda(application(bound(0), bound(1)))
    expect(termEq(shift(1, 0, term), lambda(application(bound(0), bound(2))))).toBe(true)
    expect(termEq(
      shift(1, 2, application(bound(0), application(bound(1), bound(2)))),
      application(bound(0), application(bound(1), bound(3))),
    )).toBe(true)
  })

  it('leaves canonical free slots untouched', () => {
    expect(termEq(shift(2, 0, application(free(0), bound(0))), application(free(0), bound(2))))
      .toBe(true)
  })

  it('rejects a shift that would produce a negative index', () => {
    expect(() => shift(-1, 0, bound(0))).toThrowError(/negative index/i)
    expect(() => shift(-2, 0, bound(1))).toThrowError(/negative index/i)
  })
})

describe('betaReduce', () => {
  it('substitutes every occurrence of the binder', () => {
    expect(termEq(
      betaReduce(application(bound(0), bound(0)), free(0)),
      application(free(0), free(0)),
    )).toBe(true)
  })

  it('avoids capture and handles multiple escaping indices under nested binders', () => {
    expect(termEq(betaReduce(lambda(bound(1)), bound(0)), lambda(bound(1)))).toBe(true)
    expect(termEq(
      betaReduce(lambda(bound(1)), application(bound(0), bound(1))),
      lambda(application(bound(1), bound(2))),
    )).toBe(true)
  })

  it('decrements indices above the removed binder and drops unused arguments', () => {
    expect(termEq(betaReduce(bound(1), free(0)), bound(0))).toBe(true)
    expect(termEq(betaReduce(free(0), application(free(1), free(1))), free(0))).toBe(true)
  })
})
