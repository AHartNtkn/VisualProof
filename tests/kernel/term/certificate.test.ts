import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { checkConversion, type ConversionCertificate } from '../../../src/kernel/term/certificate'
import {
  checkNormalSeparation,
  type NormalSeparationCertificate,
} from '../../../src/kernel/term'

const p = (s: string) => parseTerm(s)

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

  it('rejects an invalid right step, naming the side and step index', () => {
    const cert: ConversionCertificate = {
      leftSteps: [],
      rightSteps: [{ kind: 'beta', path: ['fn', 'fn'] }],
    }
    const result = checkConversion(YF, F_YF, cert)
    expect(result.ok).toBe(false)
    if (!result.ok) {
      expect(result.reason).toMatch(/right step 0/i)
    }
  })

  it('accepts the trivial certificate for identical terms', () => {
    const result = checkConversion(Y, Y, { leftSteps: [], rightSteps: [] })
    expect(result.ok).toBe(true)
  })
})

describe('checkNormalSeparation', () => {
  it('accepts empty paths to arbitrary distinct closed beta-eta normal terms', () => {
    const certificate: NormalSeparationCertificate = { firstSteps: [], secondSteps: [] }

    expect(checkNormalSeparation(p('\\x. x'), p('\\x. \\y. x'), certificate)).toMatchObject({
      ok: true,
      firstNormal: p('\\x. x'),
      secondNormal: p('\\x. \\y. x'),
    })
  })

  it('replays explicit beta and eta paths and returns their normal endpoints', () => {
    const certificate: NormalSeparationCertificate = {
      firstSteps: [{ kind: 'beta', path: [] }],
      secondSteps: [{ kind: 'eta', path: [] }],
    }

    expect(
      checkNormalSeparation(
        p('(\\x. x) (\\z. z)'),
        p('\\x. (\\a. \\b. a) x'),
        certificate,
      ),
    ).toMatchObject({
      ok: true,
      firstNormal: p('\\z. z'),
      secondNormal: p('\\a. \\b. a'),
    })
  })

  it('rejects an invalid first path with its side and zero-based step index', () => {
    const result = checkNormalSeparation(p('\\x. x'), p('\\x. \\y. x'), {
      firstSteps: [{ kind: 'beta', path: [] }],
      secondSteps: [],
    })

    expect(result).toMatchObject({ ok: false, reason: expect.stringMatching(/first step 0/i) })
  })

  it('rejects an invalid second path with its side and zero-based step index', () => {
    const result = checkNormalSeparation(p('\\x. x'), p('(\\x. x) (\\z. z)'), {
      firstSteps: [],
      secondSteps: [
        { kind: 'beta', path: [] },
        { kind: 'beta', path: [] },
      ],
    })

    expect(result).toMatchObject({ ok: false, reason: expect.stringMatching(/second step 1/i) })
  })

  it('rejects a beta-reducible first endpoint', () => {
    const result = checkNormalSeparation(p('(\\x. x) (\\z. z)'), p('\\x. \\y. x'), {
      firstSteps: [],
      secondSteps: [],
    })

    expect(result).toMatchObject({
      ok: false,
      reason: expect.stringMatching(/first.*does not end in beta-eta normal form/i),
    })
  })

  it('rejects an eta-reducible second endpoint', () => {
    const result = checkNormalSeparation(p('\\x. x'), p('\\x. (\\y. y) x'), {
      firstSteps: [],
      secondSteps: [],
    })

    expect(result).toMatchObject({
      ok: false,
      reason: expect.stringMatching(/second.*does not end in beta-eta normal form/i),
    })
  })

  it('rejects equal beta-eta normal endpoints', () => {
    const result = checkNormalSeparation(p('\\x. x'), p('\\y. y'), {
      firstSteps: [],
      secondSteps: [],
    })

    expect(result).toMatchObject({
      ok: false,
      reason: expect.stringMatching(/same normal form/i),
    })
  })
})
