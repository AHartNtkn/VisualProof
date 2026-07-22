import { describe, expect, it } from 'vitest'
import {
  TERM,
  relSig,
  sigEquals,
  sigKey,
  sigOrder,
  assertWellFormedSig,
  SigError,
} from '../../../src/kernel/diagram/sig'

describe('Sig module', () => {
  describe('TERM constant', () => {
    it('has kind "term"', () => {
      expect(TERM.kind).toBe('term')
    })

    it('is immutable (readonly)', () => {
      expect(() => {
        ;(TERM as any).kind = 'rel'
      }).toThrow()
    })
  })

  describe('relSig constructor', () => {
    it('creates a rel signature with empty args', () => {
      const sig = relSig([])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toEqual([])
    })

    it('creates a rel signature with one term arg', () => {
      const sig = relSig([TERM])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toHaveLength(1)
      expect(sig.args[0]).toBe(TERM)
    })

    it('creates a rel signature with nested rel and term args', () => {
      const innerRel = relSig([TERM])
      const sig = relSig([innerRel, TERM])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toHaveLength(2)
      expect(sig.args[0]).toBe(innerRel)
      expect(sig.args[1]).toBe(TERM)
    })

    it('returns a RelSig type (Extract works correctly)', () => {
      const sig = relSig([TERM])
      // RelSig is Extract<Sig, { kind: 'rel' }>
      expect(sig.kind).toBe('rel')
      expect(sig.args).toBeDefined()
    })
  })

  describe('sigEquals structural equality', () => {
    it('two TERM references are equal', () => {
      expect(sigEquals(TERM, TERM)).toBe(true)
    })

    it('two identical empty rel signatures are equal', () => {
      const sig1 = relSig([])
      const sig2 = relSig([])
      expect(sigEquals(sig1, sig2)).toBe(true)
    })

    it('two rel signatures with same structure are equal', () => {
      const sig1 = relSig([TERM])
      const sig2 = relSig([TERM])
      expect(sigEquals(sig1, sig2)).toBe(true)
    })

    it('nested structures are compared structurally', () => {
      const sig1 = relSig([relSig([TERM]), TERM])
      const sig2 = relSig([relSig([TERM]), TERM])
      expect(sigEquals(sig1, sig2)).toBe(true)
    })

    it('TERM and rel() are not equal', () => {
      const rel = relSig([])
      expect(sigEquals(TERM, rel)).toBe(false)
    })

    it('rel() and rel(term) are not equal', () => {
      const rel1 = relSig([])
      const rel2 = relSig([TERM])
      expect(sigEquals(rel1, rel2)).toBe(false)
    })

    it('rel(term) and rel(rel(term)) are not equal', () => {
      const rel1 = relSig([TERM])
      const rel2 = relSig([relSig([TERM])])
      expect(sigEquals(rel1, rel2)).toBe(false)
    })
  })

  describe('sigKey canonical string representation', () => {
    it('returns "t" for TERM', () => {
      expect(sigKey(TERM)).toBe('t')
    })

    it('returns "()" for empty rel', () => {
      expect(sigKey(relSig([]))).toBe('()')
    })

    it('returns "(t)" for rel with one term', () => {
      expect(sigKey(relSig([TERM]))).toBe('(t)')
    })

    it('returns "(t,t)" for rel with two terms', () => {
      expect(sigKey(relSig([TERM, TERM]))).toBe('(t,t)')
    })

    it('returns "((t),t)" for rel with nested rel and term', () => {
      const innerRel = relSig([TERM])
      expect(sigKey(relSig([innerRel, TERM]))).toBe('((t),t)')
    })

    it('is injective across different signatures', () => {
      const sigs = [
        TERM,
        relSig([]),
        relSig([TERM]),
        relSig([TERM, TERM]),
        relSig([relSig([TERM])]),
        relSig([relSig([TERM]), TERM]),
        relSig([relSig([TERM]), relSig([TERM])]),
        relSig([relSig([relSig([TERM])])]),
      ]
      const keys = sigs.map(sigKey)
      // All keys should be unique
      const uniqueKeys = new Set(keys)
      expect(uniqueKeys.size).toBe(keys.length)
    })

    it('produces different keys for Arrow sort example', () => {
      // Arrow sort: ((ι),(ι),ι) spelled as relSig([relSig([TERM]), relSig([TERM]), TERM])
      const arrowSig = relSig([relSig([TERM]), relSig([TERM]), TERM])
      const key = sigKey(arrowSig)
      expect(key).toBe('((t),(t),t)')

      // Verify it's different from simpler structures
      expect(key).not.toBe('(t,t,t)')
      expect(key).not.toBe('((t),(t))')
      expect(key).not.toBe('(t)')
    })
  })

  describe('sigOrder depth calculation', () => {
    it('returns 0 for TERM', () => {
      expect(sigOrder(TERM)).toBe(0)
    })

    it('returns 1 for empty rel', () => {
      expect(sigOrder(relSig([]))).toBe(1)
    })

    it('returns 1 for rel with one term', () => {
      expect(sigOrder(relSig([TERM]))).toBe(1)
    })

    it('returns 1 for rel with two terms', () => {
      expect(sigOrder(relSig([TERM, TERM]))).toBe(1)
    })

    it('returns 2 for rel with nested rel and term', () => {
      const innerRel = relSig([TERM])
      const sig = relSig([innerRel, TERM])
      expect(sigOrder(sig)).toBe(2)
    })

    it('returns correct order for deeply nested rel', () => {
      const l1 = relSig([TERM])
      const l2 = relSig([l1])
      const l3 = relSig([l2])
      expect(sigOrder(l1)).toBe(1)
      expect(sigOrder(l2)).toBe(2)
      expect(sigOrder(l3)).toBe(3)
    })

    it('returns order based on max depth for multiple args', () => {
      // rel(term, term) = order 1
      const sig1 = relSig([TERM, TERM])
      expect(sigOrder(sig1)).toBe(1)

      // rel(rel(term), term) = order 2
      const sig2 = relSig([relSig([TERM]), TERM])
      expect(sigOrder(sig2)).toBe(2)

      // rel(rel(term), rel(term)) = order 2
      const sig3 = relSig([relSig([TERM]), relSig([TERM])])
      expect(sigOrder(sig3)).toBe(2)

      // rel(rel(rel(term)), rel(term)) = order 3
      const sig4 = relSig([relSig([relSig([TERM])]), relSig([TERM])])
      expect(sigOrder(sig4)).toBe(3)
    })

    it('Arrow sort example has order 2', () => {
      const arrowSig = relSig([relSig([TERM]), relSig([TERM]), TERM])
      expect(sigOrder(arrowSig)).toBe(2)
    })
  })

  describe('assertWellFormedSig type guard', () => {
    it('accepts TERM', () => {
      expect(() => assertWellFormedSig(TERM)).not.toThrow()
    })

    it('accepts valid rel signatures', () => {
      expect(() => assertWellFormedSig(relSig([]))).not.toThrow()
      expect(() => assertWellFormedSig(relSig([TERM]))).not.toThrow()
      expect(() => assertWellFormedSig(relSig([TERM, TERM]))).not.toThrow()
      expect(() => assertWellFormedSig(relSig([relSig([TERM])]))).not.toThrow()
    })

    it('throws on missing kind property', () => {
      expect(() => assertWellFormedSig({ args: [] })).toThrow(SigError)
    })

    it('throws on invalid kind value', () => {
      expect(() => assertWellFormedSig({ kind: 'invalid' })).toThrow(SigError)
    })

    it('throws on rel with non-array args', () => {
      expect(() => assertWellFormedSig({ kind: 'rel', args: 'x' })).toThrow(SigError)
    })

    it('throws on rel with null args', () => {
      expect(() => assertWellFormedSig({ kind: 'rel', args: null })).toThrow(SigError)
    })

    it('throws on rel with object args', () => {
      expect(() => assertWellFormedSig({ kind: 'rel', args: { length: 1 } })).toThrow(SigError)
    })

    it('throws on rel with non-Sig array elements', () => {
      expect(() => assertWellFormedSig({ kind: 'rel', args: [{ kind: 'invalid' }] })).toThrow(SigError)
    })

    it('error has name "SigError"', () => {
      try {
        assertWellFormedSig({ kind: 'rel', args: 'x' })
      } catch (e) {
        expect(e).toBeInstanceOf(SigError)
        expect((e as Error).name).toBe('SigError')
      }
    })

    it('error messages are specific and loud', () => {
      try {
        assertWellFormedSig({ kind: 'rel', args: 'x' })
        expect.fail('should have thrown')
      } catch (e) {
        expect((e as Error).message).toMatch(/args|array|rel/i)
      }
    })

    it('error messages indicate what was wrong', () => {
      try {
        assertWellFormedSig({ kind: 'invalid' })
        expect.fail('should have thrown')
      } catch (e) {
        expect((e as Error).message).toMatch(/kind|invalid/i)
      }
    })
  })
})
