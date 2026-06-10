import { describe, it, expect } from 'vitest'
import { bvar, port, lam, app, termEq } from '../../../src/kernel/term/term'
import { stepNormalOrder, applyStepAt } from '../../../src/kernel/term/reduce'
import { parseTerm } from '../../../src/kernel/term/parse'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('stepNormalOrder', () => {
  it('returns null for terms in beta-normal form', () => {
    expect(stepNormalOrder(p('\\x. x'))).toBeNull()
    expect(stepNormalOrder(p('f (g a)'))).toBeNull()
  })

  it('reduces the leftmost-outermost redex first', () => {
    // (\x. x) ((\y. y) a) — outer redex reduces first, path is []
    const t = p('(\\x. x) ((\\y. y) a)')
    const r = stepNormalOrder(t)
    expect(r).not.toBeNull()
    expect(r!.path).toEqual([])
    expect(termEq(r!.term, p('(\\y. y) a'))).toBe(true)
  })

  it('reduces under lambda when no outer redex exists', () => {
    const t = p('\\x. (\\y. y) x')
    const r = stepNormalOrder(t)
    expect(r).not.toBeNull()
    expect(r!.path).toEqual(['body'])
    expect(termEq(r!.term, p('\\x. x'))).toBe(true)
  })

  it('prefers fn-side redexes over arg-side', () => {
    const t = p('((\\x. x) f) ((\\y. y) a)')
    const r = stepNormalOrder(t)
    expect(r!.path).toEqual(['fn'])
    expect(termEq(r!.term, p('f ((\\y. y) a)'))).toBe(true)
  })
})

describe('applyStepAt', () => {
  it('applies a beta step at an explicit path', () => {
    const t = p('((\\x. x) f) ((\\y. y) a)')
    const r = applyStepAt(t, { kind: 'beta', path: ['arg'] })
    expect(termEq(r, p('((\\x. x) f) a'))).toBe(true)
  })

  it('rejects a path that does not point at a redex of the claimed kind', () => {
    expect(() => applyStepAt(p('f a'), { kind: 'beta', path: [] }))
      .toThrowError(/no beta redex at path \[\]/i)
    expect(() => applyStepAt(p('\\x. x'), { kind: 'beta', path: ['fn'] }))
      .toThrowError(/invalid path segment 'fn'/i)
  })

  it('applies an eta step: \\x. f x → f when x not free in f', () => {
    const t = lam(app(port('f'), bvar(0)))
    expect(termEq(applyStepAt(t, { kind: 'eta', path: [] }), port('f'))).toBe(true)
  })

  it('rejects eta when the binder occurs in the function part', () => {
    // \x. x x is not an eta redex
    const t = lam(app(bvar(0), bvar(0)))
    expect(() => applyStepAt(t, { kind: 'eta', path: [] })).toThrowError(/no eta redex/i)
  })
})
