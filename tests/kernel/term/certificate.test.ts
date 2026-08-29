import { describe, expect, it } from 'vitest'
import {
  checkConversion,
  checkNormalSeparation,
  type ConversionCertificate,
} from '../../../src/kernel/term/certificate'
import { parseTerm } from '../../../src/kernel/term/parse'

const p = (source: string) => parseTerm(source).term
const y = p('\\f. (\\x. f (x x)) (\\x. f (x x))')
const yf = p('(\\f. (\\x. f (x x)) (\\x. f (x x))) g')
const fYf = p('g ((\\f. (\\x. f (x x)) (\\x. f (x x))) g)')

describe('conversion certificates', () => {
  it('accepts paths to a common reduct even without a normal form', () => {
    const certificate: ConversionCertificate = {
      leftSteps: [{ kind: 'beta', path: [] }, { kind: 'beta', path: [] }],
      rightSteps: [{ kind: 'beta', path: ['argument'] }],
    }
    expect(checkConversion(yf, fYf, certificate).ok).toBe(true)
    expect(checkConversion(y, y, { leftSteps: [], rightSteps: [] }).ok).toBe(true)
  })

  it('rejects tampered paths and paths that do not meet', () => {
    expect(checkConversion(yf, fYf, {
      leftSteps: [{ kind: 'beta', path: [] }],
      rightSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/do not meet/i) })
    expect(checkConversion(yf, fYf, {
      leftSteps: [{ kind: 'beta', path: ['fn', 'fn'] }],
      rightSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/left step 0/i) })
    expect(checkConversion(yf, fYf, {
      leftSteps: [],
      rightSteps: [{ kind: 'eta', path: [] }],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/right step 0/i) })
  })
})

describe('normal separation certificates', () => {
  it('accepts explicit paths to distinct beta-eta normal forms', () => {
    expect(checkNormalSeparation(
      p('(\\x. x) (\\z. z)'),
      p('\\x. (\\a. \\b. a) x'),
      {
        firstSteps: [{ kind: 'beta', path: [] }],
        secondSteps: [{ kind: 'eta', path: [] }],
      },
    )).toMatchObject({
      ok: true,
      firstNormal: p('\\z. z'),
      secondNormal: p('\\a. \\b. a'),
    })
  })

  it('rejects tampered paths, reducible endpoints, and equal endpoints', () => {
    expect(checkNormalSeparation(p('\\x. x'), p('\\x. \\y. x'), {
      firstSteps: [{ kind: 'beta', path: [] }], secondSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/first step 0/i) })
    expect(checkNormalSeparation(p('\\x. x'), p('(\\x. x) (\\z. z)'), {
      firstSteps: [], secondSteps: [{ kind: 'beta', path: [] }, { kind: 'beta', path: [] }],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/second step 1/i) })
    expect(checkNormalSeparation(p('(\\x. x) (\\z. z)'), p('\\x. \\y. x'), {
      firstSteps: [], secondSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/first.*normal form/i) })
    expect(checkNormalSeparation(p('\\x. x'), p('\\x. (\\y. y) x'), {
      firstSteps: [], secondSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/second.*normal form/i) })
    expect(checkNormalSeparation(p('\\x. x'), p('\\y. y'), {
      firstSteps: [], secondSteps: [],
    })).toMatchObject({ ok: false, reason: expect.stringMatching(/same normal form/i) })
  })
})
