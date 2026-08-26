import { describe, expect, it } from 'vitest'
import { checkConversion } from '../../../src/kernel/term/certificate'
import { headNormalize, headSpine, weakHeadNormalize } from '../../../src/kernel/term/hnf'
import { parseTerm } from '../../../src/kernel/term/parse'
import { bound, free, termEq } from '../../../src/kernel/term/term'

const p = (source: string) => parseTerm(source).term
const omega = p('(\\x. x x) (\\x. x x)')

describe('headSpine', () => {
  it('analyzes binder prefixes, canonical free heads, bound heads, and arguments', () => {
    const freeHead = headSpine(p('\\x. f x y'))
    expect(freeHead).toMatchObject({ binders: 1, head: { kind: 'free', slot: 0 } })
    expect(freeHead.args).toHaveLength(2)
    expect(termEq(freeHead.args[0]!, bound(0))).toBe(true)
    expect(termEq(freeHead.args[1]!, free(1))).toBe(true)

    expect(headSpine(p('\\x. \\y. x'))).toMatchObject({
      binders: 2,
      head: { kind: 'bound', index: 1 },
      args: [],
    })
    expect(headSpine(p('a'))).toMatchObject({ binders: 0, head: { kind: 'free', slot: 0 }, args: [] })
  })

  it('recognizes a lambda in applied head position as a redex', () => {
    expect(headSpine(p('(\\u. u) y')).head).toEqual({ kind: 'redex' })
    expect(headSpine(p('\\x. (\\u. u) x')).head).toEqual({ kind: 'redex' })
    expect(headSpine(p('((\\u. u) f) x y')).args).toHaveLength(3)
  })
})

describe('head normalization', () => {
  it('reduces only the head and produces checkable steps', () => {
    const term = p('(\\u. \\v. u) a b')
    const trace = headNormalize(term, 2)
    expect(termEq(trace.term, p('a'))).toBe(true)
    expect(trace.steps).toHaveLength(2)
    expect(checkConversion(term, trace.term, { leftSteps: trace.steps, rightSteps: [] }).ok).toBe(true)

    const rigid = p('f ((\\u. u) a) b')
    expect(headNormalize(rigid, 100)).toEqual({ term: rigid, steps: [] })
  })

  it('descends under binders while weak head normalization stops there', () => {
    const term = p('\\x. (\\u. u) x')
    expect(headNormalize(term, 100)).toMatchObject({
      term: p('\\x. x'),
      steps: [{ kind: 'beta', path: ['body'] }],
    })
    expect(weakHeadNormalize(term, 100)).toEqual({ term, steps: [] })
  })

  it('weakly reduces until a lambda or rigid head is exposed', () => {
    const term = p('(\\u. u) (\\x. (\\v. v) x)')
    expect(weakHeadNormalize(term, 100)).toMatchObject({
      term: p('\\x. (\\v. v) x'),
      steps: [{ kind: 'beta', path: [] }],
    })
    expect(weakHeadNormalize(p('f a'), 100).steps).toHaveLength(0)
  })

  it('enforces exact positive fuel budgets for divergent heads', () => {
    expect(() => headNormalize(omega, 50)).toThrowError(/fuel.*50/i)
    expect(() => weakHeadNormalize(omega, 10)).toThrowError(/fuel.*10/i)
    expect(() => headNormalize(p('a'), 0)).toThrowError(/positive integer/i)
    expect(() => weakHeadNormalize(p('a'), -1)).toThrowError(/positive integer/i)
  })
})
