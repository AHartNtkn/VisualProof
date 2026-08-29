import { describe, expect, it } from 'vitest'
import { application, bound, free, lambda, termEq } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { applyStepAt, hasFreeBound, stepNormalOrder } from '../../../src/kernel/term/reduce'

const p = (source: string) => parseTerm(source).term

describe('normal-order and explicit reduction steps', () => {
  it('finds the leftmost-outermost beta redex, descending through structural paths', () => {
    const outer = stepNormalOrder(p('(\\x. x) ((\\y. y) a)'))
    expect(outer?.path).toEqual([])
    expect(termEq(outer!.term, p('(\\y. y) a'))).toBe(true)

    const body = stepNormalOrder(p('\\x. (\\y. y) x'))
    expect(body?.path).toEqual(['body'])
    expect(termEq(body!.term, p('\\x. x'))).toBe(true)

    const fn = stepNormalOrder(p('((\\x. x) f) ((\\y. y) a)'))
    expect(fn?.path).toEqual(['fn'])
  })

  it('returns null in beta normal form and steps Omega to itself', () => {
    expect(stepNormalOrder(p('\\x. x'))).toBeNull()
    const omega = p('(\\x. x x) (\\x. x x)')
    expect(termEq(stepNormalOrder(omega)!.term, omega)).toBe(true)
  })

  it('replays beta and eta steps at exact paths', () => {
    expect(termEq(
      applyStepAt(p('((\\x. x) f) ((\\y. y) a)'), { kind: 'beta', path: ['argument'] }),
      p('((\\x. x) f) a'),
    )).toBe(true)
    expect(termEq(
      applyStepAt(lambda(application(free(0), bound(0))), { kind: 'eta', path: [] }),
      free(0),
    )).toBe(true)
    expect(termEq(
      applyStepAt(lambda(lambda(application(free(0), bound(0)))), { kind: 'eta', path: ['body'] }),
      lambda(free(0)),
    )).toBe(true)
  })

  it('rejects mismatched paths, beta claims, and eta capture', () => {
    expect(() => applyStepAt(p('f a'), { kind: 'beta', path: [] })).toThrowError(/no beta redex/i)
    expect(() => applyStepAt(p('\\x. x'), { kind: 'beta', path: ['fn'] })).toThrowError(/invalid path segment/i)
    expect(() => applyStepAt(lambda(application(bound(0), bound(0))), { kind: 'eta', path: [] }))
      .toThrowError(/no eta redex/i)
  })

  it('tracks escaping bound indices through binders', () => {
    expect(hasFreeBound(0, lambda(bound(1)))).toBe(true)
    expect(hasFreeBound(0, lambda(bound(0)))).toBe(false)
    expect(hasFreeBound(0, lambda(lambda(bound(2))))).toBe(true)
  })
})
