import { describe, expect, it } from 'vitest'
import {
  IOTA,
  relSig,
  sigEquals,
  sigKey,
  sigOrder,
  assertWellFormedSig,
  SigError,
} from '../../../src/kernel/diagram/sig'

describe('Sig module', () => {
  describe('IOTA constant', () => {
    it('has kind "iota"', () => {
      expect(IOTA.kind).toBe('iota')
    })

    it('is immutable (readonly)', () => {
      expect(() => {
        ;(IOTA as any).kind = 'rel'
      }).toThrow()
    })
  })

  describe('relSig constructor', () => {
    it('creates a rel signature with empty args', () => {
      const sig = relSig([])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toEqual([])
    })

    it('creates a rel signature with one iota arg', () => {
      const sig = relSig([IOTA])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toHaveLength(1)
      expect(sig.args[0]).toBe(IOTA)
    })

    it('creates a rel signature with nested rel and iota args', () => {
      const innerRel = relSig([IOTA])
      const sig = relSig([innerRel, IOTA])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toHaveLength(2)
      expect(sig.args[0]).toBe(innerRel)
      expect(sig.args[1]).toBe(IOTA)
    })

    it('returns a RelSig type (Extract works correctly)', () => {
      const sig = relSig([IOTA])
      expect(sig.kind).toBe('rel')
      expect(sig.args).toBeDefined()
    })
  })

  describe('sigEquals structural equality', () => {
    it('recognizes iota structurally', () => {
      expect(sigEquals(IOTA, IOTA)).toBe(true)
      expect(sigEquals(IOTA, { kind: 'iota' })).toBe(true)
    })

    it('two identical empty rel signatures are equal', () => {
      expect(sigEquals(relSig([]), relSig([]))).toBe(true)
    })

    it('compares nested structures structurally', () => {
      const sig1 = relSig([relSig([IOTA]), IOTA])
      const sig2 = relSig([relSig([IOTA]), IOTA])
      expect(sigEquals(sig1, sig2)).toBe(true)
      expect(sigEquals(IOTA, relSig([]))).toBe(false)
      expect(sigEquals(relSig([IOTA]), relSig([relSig([IOTA])]))).toBe(false)
    })
  })

  describe('sigKey canonical string representation', () => {
    it('returns "i" for IOTA', () => {
      expect(sigKey(IOTA)).toBe('i')
    })

    it('encodes relation signatures recursively', () => {
      expect(sigKey(relSig([]))).toBe('()')
      expect(sigKey(relSig([IOTA]))).toBe('(i)')
      expect(sigKey(relSig([IOTA, IOTA]))).toBe('(i,i)')
      expect(sigKey(relSig([IOTA, relSig([IOTA])]))).toBe('(i,(i))')
    })

    it('is injective across different signatures', () => {
      const sigs = [
        IOTA,
        relSig([]),
        relSig([IOTA]),
        relSig([IOTA, IOTA]),
        relSig([relSig([IOTA])]),
        relSig([relSig([IOTA]), IOTA]),
        relSig([relSig([IOTA]), relSig([IOTA])]),
        relSig([relSig([relSig([IOTA])])]),
      ]
      const keys = sigs.map(sigKey)
      expect(new Set(keys).size).toBe(keys.length)
    })
  })

  describe('sigOrder depth calculation', () => {
    it('returns 0 for IOTA and increases for nested rel signatures', () => {
      const l1 = relSig([IOTA])
      const l2 = relSig([l1])
      const l3 = relSig([l2])
      expect(sigOrder(IOTA)).toBe(0)
      expect(sigOrder(relSig([]))).toBe(1)
      expect(sigOrder(l1)).toBe(1)
      expect(sigOrder(l2)).toBe(2)
      expect(sigOrder(l3)).toBe(3)
    })
  })

  describe('assertWellFormedSig type guard', () => {
    it('accepts IOTA and valid rel signatures', () => {
      expect(() => assertWellFormedSig(IOTA)).not.toThrow()
      expect(() => assertWellFormedSig(relSig([]))).not.toThrow()
      expect(() => assertWellFormedSig(relSig([IOTA, relSig([IOTA])]))).not.toThrow()
    })

    it('rejects malformed and legacy signatures', () => {
      expect(() => assertWellFormedSig({ args: [] })).toThrow(SigError)
      expect(() => assertWellFormedSig({ kind: 'term' })).toThrow(SigError)
      expect(() => assertWellFormedSig({ kind: 'rel', args: 'x' })).toThrow(SigError)
      expect(() => assertWellFormedSig({ kind: 'rel', args: [{ kind: 'invalid' }] })).toThrow(SigError)
    })
  })
})
