import { describe, expect, it } from 'vitest'
import {
  application,
  assertWellFormedTerm,
  bound,
  free,
  freeArity,
  lambda,
  termEq,
} from '../../../src/kernel/term/term'

describe('nameless term structure', () => {
  it('makes alpha equality structural and distinguishes free slots', () => {
    expect(termEq(lambda(bound(0)), lambda(bound(0)))).toBe(true)
    expect(termEq(lambda(bound(0)), lambda(lambda(bound(0))))).toBe(false)
    expect(termEq(free(0), free(1))).toBe(false)
  })

  it('rejects invalid indices and slots at construction', () => {
    expect(() => bound(-1)).toThrowError(/negative/i)
    expect(() => bound(0.5)).toThrowError(/fractional/i)
    expect(() => bound(2 ** 53)).toThrowError(/safe integer/i)
    expect(() => free(-1)).toThrowError(/negative/i)
    expect(() => free(0.5)).toThrowError(/fractional/i)
    expect(() => free(2 ** 53)).toThrowError(/safe integer/i)
  })

  it('derives the smallest numeric free interface', () => {
    expect(freeArity(lambda(application(free(2), application(free(0), bound(0)))))).toBe(3)
    expect(freeArity(lambda(bound(0)))).toBe(0)
  })

  it('validates binder scope and an explicit free interface', () => {
    const term = lambda(application(bound(0), free(1)))
    expect(() => assertWellFormedTerm(term)).not.toThrow()
    expect(() => assertWellFormedTerm(term, 2)).not.toThrow()
    expect(() => assertWellFormedTerm(term, 1)).toThrowError(/free slot 1.*arity 1/i)
    expect(() => assertWellFormedTerm({ kind: 'bound', index: 0 })).toThrowError(/unbound de Bruijn index 0/i)
    expect(() => assertWellFormedTerm({ kind: 'free', slot: -1 })).toThrowError(/non-negative safe integer/i)
    expect(() => assertWellFormedTerm(term, -1)).toThrowError(/interface arity.*non-negative safe integer/i)
  })
})
