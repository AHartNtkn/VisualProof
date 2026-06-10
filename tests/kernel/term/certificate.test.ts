import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { checkConversion, type ConversionCertificate } from '../../../src/kernel/term/certificate'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

const Y = p('\\f. (\\x. f (x x)) (\\x. f (x x))')
const YF = p('(\\f. (\\x. f (x x)) (\\x. f (x x))) g')         // Y g
const F_YF = p('g ((\\f. (\\x. f (x x)) (\\x. f (x x))) g)')   // g (Y g)

describe('checkConversion', () => {
  it('accepts Y g = g (Y g) via paths to a common reduct, despite no normal form existing', () => {
    // Y g →β (\x. g (x x)) (\x. g (x x)) →β g ((\x. g (x x)) (\x. g (x x)))
    // g (Y g) →β(inside arg) g ((\x. g (x x)) (\x. g (x x)))
    const cert: ConversionCertificate = {
      leftSteps: [
        { kind: 'beta', path: [] },
        { kind: 'beta', path: [] },
      ],
      rightSteps: [
        { kind: 'beta', path: ['arg'] },
      ],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok, result.ok ? '' : result.reason).toBe(true)
  })

  it('rejects a certificate whose paths do not meet', () => {
    const cert: ConversionCertificate = {
      leftSteps: [{ kind: 'beta', path: [] }],
      rightSteps: [],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/do not meet/i)
    }
  })

  it('rejects a certificate with an invalid step, naming the side and step index', () => {
    const cert: ConversionCertificate = {
      leftSteps: [{ kind: 'beta', path: ['fn', 'fn'] }],
      rightSteps: [],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/left step 0/i)
    }
  })

  it('accepts the trivial certificate for identical terms', () => {
    const result = checkConversion(Y, Y, { leftSteps: [], rightSteps: [] })
    expect(result.ok).toBe(true)
  })
})
