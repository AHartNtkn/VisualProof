import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { termShapeKey, positionalPortKey } from '../../../src/kernel/diagram/canonical/shape'

const p = (s: string) => parseTerm(s)

describe('termShapeKey', () => {
  it('is invariant under free-variable renaming (positional relation identity)', () => {
    expect(termShapeKey(p('y z'))).toBe(termShapeKey(p('a b')))
    expect(termShapeKey(p('y (z y)'))).toBe(termShapeKey(p('z (y z)')))
    expect(termShapeKey(p('\\x. y x'))).toBe(termShapeKey(p('\\q. w q')))
  })

  it('distinguishes different positional relations', () => {
    // one free var used twice vs two distinct free vars
    expect(termShapeKey(p('y y'))).not.toBe(termShapeKey(p('y z')))
    // structure matters
    expect(termShapeKey(p('\\x. x'))).not.toBe(termShapeKey(p('\\x. \\y. x')))
  })

  it('renames ports as p0, p1 in first-occurrence order', () => {
    expect(termShapeKey(p('y z'))).toBe('2:A(P("p0"),P("p1"))')
    expect(termShapeKey(p('z y'))).toBe('2:A(P("p0"),P("p1"))') // same positional relation
  })

  it('includes unused declared positions in shape and positional port keys', () => {
    expect(termShapeKey(p('used'), ['unused', 'used']))
      .toBe(termShapeKey(p('b'), ['a', 'b']))
    expect(termShapeKey(p('used'), ['unused', 'used']))
      .not.toBe(termShapeKey(p('used'), ['used']))
    expect(positionalPortKey(p('used'), { kind: 'freeVar', name: 'unused' }, ['unused', 'used']))
      .toBe('v0')
  })

  it('rejects malformed terms loudly', () => {
    expect(() => termShapeKey({ kind: 'bvar', index: 0 })).toThrowError(/unbound de Bruijn index/)
  })
})

describe('positionalPortKey', () => {
  it('maps output to out, freeVar names to v{first-occurrence index}, args to a{index}', () => {
    const t = p('y (z y)') // first occurrence order: y, z
    expect(positionalPortKey(t, { kind: 'output' })).toBe('out')
    expect(positionalPortKey(t, { kind: 'freeVar', name: 'y' })).toBe('v0')
    expect(positionalPortKey(t, { kind: 'freeVar', name: 'z' })).toBe('v1')
    expect(positionalPortKey(t, { kind: 'arg', index: 3 })).toBe('a3')
  })

  it('throws for a freeVar name outside the declared interface', () => {
    expect(() => positionalPortKey(p('y'), { kind: 'freeVar', name: 'zz' }))
      .toThrowError(/'zz' is not a declared free port of the term node/)
  })
})
