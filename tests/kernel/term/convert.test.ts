import { describe, expect, it } from 'vitest'
import { checkConversion } from '../../../src/kernel/term/certificate'
import { convertible } from '../../../src/kernel/term/convert'
import { parseTerm } from '../../../src/kernel/term/parse'

const p = (source: string) => parseTerm(source).term

describe('interactive conversion search', () => {
  it('finds beta and eta conversions with checkable certificates', () => {
    const onePlusOne = p('(\\m. \\n. \\f. \\x. m f (n f x)) (\\f. \\x. f x) (\\f. \\x. f x)')
    const two = p('\\f. \\x. f (f x)')
    const beta = convertible(onePlusOne, two, 1000)
    expect(beta.status).toBe('convertible')
    if (beta.status === 'convertible') {
      expect(checkConversion(onePlusOne, two, beta.certificate).ok).toBe(true)
    }

    const etaLeft = p('\\x. f x')
    const etaRight = p('f')
    const eta = convertible(etaLeft, etaRight, 100)
    expect(eta.status).toBe('convertible')
    if (eta.status === 'convertible') {
      expect(checkConversion(etaLeft, etaRight, eta.certificate).ok).toBe(true)
    }
  })

  it('separates distinct normal forms', () => {
    expect(convertible(p('\\f. \\x. f x'), p('\\f. \\x. f (f x)'), 100).status)
      .toBe('not-convertible')
  })

  it('reports which side exhausted fuel without guessing', () => {
    const omega = p('(\\x. x x) (\\x. x x)')
    expect(convertible(omega, p('\\x. x'), 25)).toMatchObject({
      status: 'fuel-exhausted', detail: expect.stringMatching(/left/i),
    })
    expect(convertible(p('\\x. x'), omega, 25)).toMatchObject({
      status: 'fuel-exhausted', detail: expect.stringMatching(/right/i),
    })
  })
})
