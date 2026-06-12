import { describe, it, expect } from 'vitest'
import { bvar, port, termEq } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'
import { checkConversion } from '../../../src/kernel/term/certificate'
import { headSpine, headNormalize, weakHeadNormalize } from '../../../src/kernel/term/hnf'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)
const pc = (s: string) => parseTerm(s, new Set(['PLUS']))

const OMEGA = p('(\\x. x x) (\\x. x x)')

describe('headSpine', () => {
  it('analyzes \\x. f x y: one binder, free head, two args', () => {
    const s = headSpine(p('\\x. f x y'))
    expect(s.binders).toBe(1)
    expect(s.head).toEqual({ kind: 'free', name: 'f' })
    expect(s.args.length).toBe(2)
    expect(termEq(s.args[0]!, bvar(0))).toBe(true)
    expect(termEq(s.args[1]!, port('y'))).toBe(true)
  })

  it('analyzes \\x. x y: bound head with de Bruijn index 0', () => {
    const s = headSpine(p('\\x. x y'))
    expect(s.binders).toBe(1)
    expect(s.head).toEqual({ kind: 'bound', index: 0 })
    expect(s.args.length).toBe(1)
    expect(termEq(s.args[0]!, port('y'))).toBe(true)
  })

  it('resolves bound heads through nested binders: \\x. \\y. x has index 1', () => {
    const s = headSpine(p('\\x. \\y. x'))
    expect(s.binders).toBe(2)
    expect(s.head).toEqual({ kind: 'bound', index: 1 })
    expect(s.args.length).toBe(0)
  })

  it('analyzes PLUS a b: const head carrying the constId', () => {
    const s = headSpine(pc('PLUS a b'))
    expect(s.binders).toBe(0)
    expect(s.head).toEqual({ kind: 'const', constId: 'PLUS' })
    expect(s.args.length).toBe(2)
  })

  it('reports a redex head for (\\u. u) y', () => {
    const s = headSpine(p('(\\u. u) y'))
    expect(s.binders).toBe(0)
    expect(s.head).toEqual({ kind: 'redex' })
    expect(s.args.length).toBe(1)
  })

  it('reports a redex head under a binder prefix: \\x. (\\u. u) x', () => {
    const s = headSpine(p('\\x. (\\u. u) x'))
    expect(s.binders).toBe(1)
    expect(s.head).toEqual({ kind: 'redex' })
    expect(s.args.length).toBe(1)
  })

  it('analyzes a bare free atom: zero binders, zero args', () => {
    const s = headSpine(p('a'))
    expect(s.binders).toBe(0)
    expect(s.head).toEqual({ kind: 'free', name: 'a' })
    expect(s.args.length).toBe(0)
  })
})

describe('headNormalize', () => {
  it('reduces (\\u. \\v. u) a b to a free head, with steps checkConversion accepts as the left certificate half', () => {
    const t = p('(\\u. \\v. u) a b')
    const r = headNormalize(t, 100)
    expect(termEq(r.term, p('a')), `expected a, got ${printTerm(r.term)}`).toBe(true)
    expect(headSpine(r.term).head.kind).toBe('free')
    expect(r.steps.length).toBe(2)
    const check = checkConversion(t, r.term, { leftSteps: r.steps, rightSteps: [] })
    expect(check.ok, check.ok ? '' : check.reason).toBe(true)
  })

  it('reduces only the head: redexes inside arguments are left untouched', () => {
    const t = p('f ((\\u. u) y)')
    const r = headNormalize(t, 100)
    expect(r.steps.length).toBe(0)
    expect(termEq(r.term, t)).toBe(true)
  })

  it('terminates at a const head without unfolding', () => {
    const t = pc('PLUS ((\\u. u) a) b')
    const r = headNormalize(t, 100)
    expect(r.steps.length).toBe(0)
    expect(termEq(r.term, t)).toBe(true)
    expect(headSpine(r.term).head).toEqual({ kind: 'const', constId: 'PLUS' })
  })

  it('descends under the binder prefix: \\x. (\\u. u) x becomes \\x. x with the body-path step recorded', () => {
    const t = p('\\x. (\\u. u) x')
    const r = headNormalize(t, 100)
    expect(termEq(r.term, p('\\x. x')), `expected \\x. x, got ${printTerm(r.term)}`).toBe(true)
    expect(r.steps).toEqual([{ kind: 'beta', path: ['body'] }])
    const check = checkConversion(t, r.term, { leftSteps: r.steps, rightSteps: [] })
    expect(check.ok, check.ok ? '' : check.reason).toBe(true)
  })

  it('clears a redex wrapping the head but does not eta-contract: \\x. ((\\u. u) f) x becomes \\x. f x', () => {
    const t = p('\\x. ((\\u. u) f) x')
    const r = headNormalize(t, 100)
    expect(termEq(r.term, p('\\x. f x')), `expected \\x. f x, got ${printTerm(r.term)}`).toBe(true)
    expect(headSpine(r.term).head.kind).toBe('free')
  })

  it('throws naming the fuel on a divergent head', () => {
    expect(() => headNormalize(OMEGA, 50)).toThrowError(/fuel/i)
    expect(() => headNormalize(OMEGA, 50)).toThrowError(/50/)
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => headNormalize(p('a'), 0)).toThrowError(/fuel must be a positive integer/i)
  })
})

describe('weakHeadNormalize', () => {
  it('stops at a top-level lambda that headNormalize would enter', () => {
    const t = p('\\x. (\\u. u) x')
    const weak = weakHeadNormalize(t, 100)
    expect(weak.steps.length).toBe(0)
    expect(termEq(weak.term, t)).toBe(true)
    const strong = headNormalize(t, 100)
    expect(termEq(strong.term, p('\\x. x'))).toBe(true)
  })

  it('reduces a top-level redex until a lambda is exposed, then stops', () => {
    const t = p('(\\u. u) (\\x. (\\v. v) x)')
    const r = weakHeadNormalize(t, 100)
    expect(r.steps.length).toBe(1)
    expect(termEq(r.term, p('\\x. (\\v. v) x')), `got ${printTerm(r.term)}`).toBe(true)
    const check = checkConversion(t, r.term, { leftSteps: r.steps, rightSteps: [] })
    expect(check.ok, check.ok ? '' : check.reason).toBe(true)
  })

  it('takes multiple head steps when no lambda intervenes: (\\u. \\v. u) a b reaches a', () => {
    const t = p('(\\u. \\v. u) a b')
    const r = weakHeadNormalize(t, 100)
    expect(termEq(r.term, p('a')), `expected a, got ${printTerm(r.term)}`).toBe(true)
    expect(r.steps.length).toBe(2)
  })

  it('terminates at a const head without unfolding', () => {
    const t = pc('PLUS a')
    const r = weakHeadNormalize(t, 100)
    expect(r.steps.length).toBe(0)
    expect(termEq(r.term, t)).toBe(true)
  })

  it('throws naming the fuel on a divergent head', () => {
    expect(() => weakHeadNormalize(OMEGA, 10)).toThrowError(/fuel/i)
    expect(() => weakHeadNormalize(OMEGA, 10)).toThrowError(/10/)
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => weakHeadNormalize(p('a'), -1)).toThrowError(/fuel must be a positive integer/i)
  })
})
