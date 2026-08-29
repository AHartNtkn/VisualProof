import { describe, expect, it } from 'vitest'
import { application, termEq, type Term } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { applyStepAt, normalize } from '../../../src/kernel/term/reduce'

const p = (source: string) => parseTerm(source).term
const chain = (...terms: Term[]) => terms.reduce((fn, argument) => application(fn, argument))

describe('normalize', () => {
  it('computes one plus one as Church two', () => {
    const zero = p('\\f. \\x. x')
    const succ = p('\\n. \\f. \\x. f (n f x)')
    const plus = p('\\m. \\n. \\f. \\x. m f (n f x)')
    const one = normalize(chain(succ, zero), 1000)
    expect(one.status).toBe('normal')
    const sum = normalize(chain(plus, one.term, one.term), 1000)
    expect(sum.status).toBe('normal')
    expect(termEq(sum.term, p('\\f. \\x. f (f x)'))).toBe(true)
  })

  it('eta-contracts after beta and records a replayable path', () => {
    const term = p('(\\f. \\x. f x) (\\y. y)')
    const result = normalize(term, 100)
    expect(result.status).toBe('normal')
    let replayed = term
    for (const step of result.path) replayed = applyStepAt(replayed, step)
    expect(termEq(replayed, result.term)).toBe(true)
    expect(termEq(result.term, p('\\y. y'))).toBe(true)
  })

  it('reports exact fuel exhaustion for Omega and during eta reduction', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const divergent = normalize(omega, 25)
    expect(divergent.status).toBe('fuel-exhausted')
    expect(divergent.path).toHaveLength(25)
    expect(termEq(divergent.term, omega)).toBe(true)

    const eta = p('\\a. \\b. f a b')
    expect(normalize(eta, 1)).toMatchObject({ status: 'fuel-exhausted', path: [{ kind: 'eta' }] })
    expect(normalize(eta, 2)).toMatchObject({ status: 'normal', path: [{ kind: 'eta' }, { kind: 'eta' }] })
  })

  it('accepts an exact one-step budget and rejects invalid fuel', () => {
    expect(normalize(p('(\\x. x) a'), 1)).toMatchObject({ status: 'normal', path: [{ kind: 'beta', path: [] }] })
    expect(() => normalize(p('\\x. x'), 0)).toThrowError(/positive integer/i)
  })
})
