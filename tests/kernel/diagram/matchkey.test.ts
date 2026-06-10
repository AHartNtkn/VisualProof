import { describe, it, expect } from 'vitest'
import { termEq } from '../../../src/kernel/term/term'
import { parseTerm } from '../../../src/kernel/term/parse'
import { closeOverPorts, termsMatchModuloBetaEta } from '../../../src/kernel/diagram/canonical/matchkey'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('closeOverPorts', () => {
  it('closes free ports as outermost lambdas in first-occurrence order', () => {
    // y z  →  \p0. \p1. p0 p1
    expect(termEq(closeOverPorts(p('y z')), p('\\a. \\b. a b'))).toBe(true)
    // y (z y)  →  \p0. \p1. p0 (p1 p0)
    expect(termEq(closeOverPorts(p('y (z y)')), p('\\a. \\b. a (b a)'))).toBe(true)
  })

  it('respects existing binders (ports skip over internal lambdas)', () => {
    // \x. y x  →  \p0. \x. p0 x
    expect(termEq(closeOverPorts(p('\\x. y x')), p('\\a. \\x. a x'))).toBe(true)
  })

  it('is the identity on closed terms', () => {
    const t = p('\\f. \\x. f (f x)')
    expect(termEq(closeOverPorts(t), t)).toBe(true)
  })

  it('rejects malformed terms loudly', () => {
    expect(() => closeOverPorts({ kind: 'bvar', index: 0 })).toThrowError(/unbound de Bruijn index/)
  })
})

describe('termsMatchModuloBetaEta', () => {
  it('matches free-variable renamings and beta-reducible forms', () => {
    expect(termsMatchModuloBetaEta(p('y z'), p('a b'), 100).status).toBe('match')
    expect(termsMatchModuloBetaEta(p('(\\x. x) (y z)'), p('y z'), 100).status).toBe('match')
  })

  it('matches eta-equal nodes of equal arity', () => {
    // node \x. f x (one port f) vs node f (one port f)
    expect(termsMatchModuloBetaEta(p('\\x. f x'), p('f'), 100).status).toBe('match')
  })

  it('rejects different arities without normalizing', () => {
    expect(termsMatchModuloBetaEta(p('y y'), p('y z'), 100).status).toBe('no-match')
  })

  it('rejects different positional relations of equal arity', () => {
    // \p0.\p1. p0 p1  vs  \p0.\p1. p0 (p0 p1) are not beta-eta-convertible
    expect(termsMatchModuloBetaEta(p('y z'), p('y (y z)'), 100).status).toBe('no-match')
  })

  it('treats naming positionally: y z and z y are the SAME relation', () => {
    // first-occurrence order puts the fn-position port at p0 in both terms;
    // names never carry content (consistent with termShapeKey)
    expect(termsMatchModuloBetaEta(p('y z'), p('z y'), 100).status).toBe('match')
  })

  it('matches identical non-normalizing terms by reflexivity (no spurious undecided)', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    expect(termsMatchModuloBetaEta(omega, omega, 25).status).toBe('match')
  })

  it('distinguishes and matches constant-carrying terms', () => {
    const pc = (s: string) => parseTerm(s, new Set(['plus', 'times']))
    expect(termsMatchModuloBetaEta(pc('plus y'), pc('times y'), 100).status).toBe('no-match')
    expect(termsMatchModuloBetaEta(pc('plus y'), pc('plus z'), 100).status).toBe('match')
  })

  it('rejects non-positive fuel as a caller error', () => {
    expect(() => termsMatchModuloBetaEta(p('y'), p('z'), 0)).toThrowError(/fuel must be a positive integer/i)
  })

  it('reports undecided on fuel exhaustion, naming the side', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const left = termsMatchModuloBetaEta(omega, p('\\x. x'), 25)
    expect(left.status).toBe('undecided')
    if (left.status === 'undecided') expect(left.detail).toMatch(/left/i)
    const right = termsMatchModuloBetaEta(p('\\x. x'), omega, 25)
    expect(right.status).toBe('undecided')
    if (right.status === 'undecided') expect(right.detail).toMatch(/right/i)
  })
})
