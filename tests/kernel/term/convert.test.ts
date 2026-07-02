import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { convertible } from '../../../src/kernel/term/convert'
import { checkConversion } from '../../../src/kernel/term/certificate'

const p = (s: string) => parseTerm(s)

describe('convertible', () => {
  it('decides 1 + 1 = 2 and returns a checkable certificate', () => {
    const onePlusOne = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)')
    const two = p('\\f. \\x. f (f x)')
    const r = convertible(onePlusOne, two, 1000)
    expect(r.status).toBe('convertible')
    if (r.status === 'convertible') {
      const check = checkConversion(onePlusOne, two, r.certificate)
      expect(check.ok, check.ok ? '' : check.reason).toBe(true)
    }
  })

  it('decides eta-equalities: \\x. f x = f, with a checkable certificate', () => {
    const left = p('\\x. f x')
    const right = p('f')
    const r = convertible(left, right, 100)
    expect(r.status).toBe('convertible')
    if (r.status === 'convertible') {
      const check = checkConversion(left, right, r.certificate)
      expect(check.ok, check.ok ? '' : check.reason).toBe(true)
    }
  })

  it('separates distinct normal forms definitively', () => {
    const r = convertible(p('\\f. \\x. f x'), p('\\f. \\x. f (f x)'), 100)
    expect(r.status).toBe('not-convertible')
  })

  it('reports fuel exhaustion distinctly — never a silent verdict', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const r = convertible(omega, p('\\x. x'), 25)
    expect(r.status).toBe('fuel-exhausted')
    if (r.status === 'fuel-exhausted') {
      expect(r.detail).toMatch(/left/i)
    }
  })

  it('names the right side when only the right side exhausts fuel', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    const r = convertible(p('\\x. x'), omega, 25)
    expect(r.status).toBe('fuel-exhausted')
    if (r.status === 'fuel-exhausted') {
      expect(r.detail).toMatch(/right/i)
    }
  })
})
