import { describe, it, expect } from 'vitest'
import { app, termEq, type Term } from '../../../src/kernel/term/term'
import { normalize, applyStepAt } from '../../../src/kernel/term/reduce'
import { parseTerm } from '../../../src/kernel/term/parse'
import { printTerm } from '../../../src/kernel/term/print'

const p = (s: string) => parseTerm(s)

const ZERO = p('\\f. \\x. x')
const SUCC = p('\\n. \\f. \\x. f (n f x)')
const PLUS = p('\\m. \\n. \\f. \\x. m f (n f x)')
const TWO = p('\\f. \\x. f (f x)')
const OMEGA = p('(\\x. x x) (\\x. x x)')

const appChain = (...ts: Term[]) => ts.reduce((a, b) => app(a, b))

describe('normalize', () => {
  it('computes 1 + 1 = 2 on Church numerals', () => {
    const one = normalize(appChain(SUCC, ZERO), 1000)
    expect(one.status).toBe('normal')
    const sum = normalize(appChain(PLUS, one.term, one.term), 1000)
    expect(sum.status).toBe('normal')
    expect(termEq(sum.term, TWO), `expected Church 2, got ${printTerm(sum.term)}`).toBe(true)
  })

  it('eta-contracts after beta: \\f. \\x. f x reaches the eta-normal form \\x0. x0', () => {
    // inner body \x. f x eta-contracts to f, leaving \f. f — the identity
    const r = normalize(p('\\f. \\x. f x'), 100)
    expect(r.status).toBe('normal')
    expect(printTerm(r.term)).toBe('\\x0. x0')
  })

  it('records the full reduction path taken', () => {
    const r = normalize(p('(\\x. x) a'), 100)
    expect(r.status).toBe('normal')
    expect(r.path.length).toBe(1)
    expect(r.path[0]).toEqual({ kind: 'beta', path: [] })
  })

  it('reports fuel exhaustion loudly with the partial term and consumed path', () => {
    const r = normalize(OMEGA, 25)
    expect(r.status).toBe('fuel-exhausted')
    expect(r.path.length).toBe(25)
    // Omega reduces to itself forever
    expect(termEq(r.term, OMEGA)).toBe(true)
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => normalize(ZERO, 0)).toThrowError(/fuel must be a positive integer/i)
  })

  it('succeeds when fuel equals the exact step count (boundary)', () => {
    // (\x. x) a needs exactly 1 beta step
    const r1 = normalize(p('(\\x. x) a'), 1)
    expect(r1.status).toBe('normal')
    expect(r1.path.length).toBe(1)

    // \f. \x. f x needs exactly 1 eta step
    const r2 = normalize(p('\\f. \\x. f x'), 1)
    expect(r2.status).toBe('normal')
    expect(r2.path.length).toBe(1)
  })

  it('reports fuel-exhausted when fuel runs out during the eta phase', () => {
    // \a. \b. f a b needs 0 beta steps and exactly 2 eta steps
    const t = p('\\a. \\b. f a b')
    const exhausted = normalize(t, 1)
    expect(exhausted.status).toBe('fuel-exhausted')
    expect(exhausted.path.length).toBe(1)
    expect(exhausted.path[0]?.kind).toBe('eta')

    const ok = normalize(t, 2)
    expect(ok.status).toBe('normal')
    expect(ok.path.length).toBe(2)
  })

  it('recorded path is replayable via applyStepAt', () => {
    const t = p('(\\f. \\x. f x) (\\y. y)')
    const r = normalize(t, 100)
    expect(r.status).toBe('normal')
    let cur = t
    for (const step of r.path) {
      cur = applyStepAt(cur, step)
    }
    expect(termEq(cur, r.term)).toBe(true)
  })
})
