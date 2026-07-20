import { describe, expect, it } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { port } from '../../../src/kernel/term/term'
import {
  proposePortCorrespondence,
  validatePortCorrespondence,
  type PortCorrespondence,
} from '../../../src/kernel/rules/port-correspondence'

const p = (source: string) => parseTerm(source)

describe('PortCorrespondence', () => {
  it('accepts an injective, exactly keyed correspondence whose union covers the common carrier', () => {
    const correspondence: PortCorrespondence = {
      commonArity: 3,
      left: { x: 0, erased: 1 },
      right: { renamed: 0, added: 2 },
    }
    expect(() => validatePortCorrespondence(correspondence, ['x', 'erased'], ['renamed', 'added']))
      .not.toThrow()
  })

  it.each([
    [{ commonArity: -1, left: {}, right: {} }, /commonArity/],
    [{ commonArity: 1.5, left: {}, right: {} }, /commonArity/],
    [{ commonArity: Number.MAX_SAFE_INTEGER + 1, left: {}, right: {} }, /commonArity/],
    [{ commonArity: 1, left: { x: -1 }, right: {} }, /safe integer.*range/],
    [{ commonArity: 1, left: { x: 1 }, right: {} }, /safe integer.*range/],
    [{ commonArity: 2, left: { x: 0, y: 0 }, right: { z: 1 } }, /injective.*left/],
    [{ commonArity: 2, left: { x: 0 }, right: { z: 0 } }, /column 1.*uncovered/],
  ] as const)('rejects malformed carrier structure %#', (correspondence, message) => {
    expect(() => validatePortCorrespondence(correspondence, Object.keys(correspondence.left), Object.keys(correspondence.right)))
      .toThrowError(message)
  })

  it('rejects missing and extra keys instead of accepting a partial or compatibility witness', () => {
    expect(() => validatePortCorrespondence(
      { commonArity: 2, left: { x: 0, stale: 1 }, right: { z: 1 } },
      ['x', 'missing'],
      ['z'],
    )).toThrowError(/left keys.*missing.*stale/)
  })

  it('proposes a deterministic native witness that pairs shared names, then remaining ports by occurrence', () => {
    expect(proposePortCorrespondence(
      p('x erased'), p('renamed added'), ['x', 'erased'], ['renamed', 'added'],
    )).toEqual({
      commonArity: 2,
      left: { x: 0, erased: 1 },
      right: { renamed: 0, added: 1 },
    })
    expect(proposePortCorrespondence(
      p('shared x'), p('shared y'), ['shared', 'x'], ['shared', 'y'],
    )).toEqual({
      commonArity: 2,
      left: { shared: 0, x: 1 },
      right: { shared: 0, y: 1 },
    })
  })

  it('treats Object prototype names as ordinary own port keys', () => {
    const names = ['toString', 'constructor', '__proto__']
    const left = Object.fromEntries(names.map((name, column) => [name, column]))
    const correspondence: PortCorrespondence = { commonArity: 3, left, right: {} }
    expect(() => validatePortCorrespondence(correspondence, names, [])).not.toThrow()

    const proposed = proposePortCorrespondence(
      port('__proto__'),
      port('__proto__'),
      names,
      names,
    )
    expect(Object.keys(proposed.left)).toEqual(names)
    expect(Object.hasOwn(proposed.left, '__proto__')).toBe(true)
    expect(proposed.left['__proto__']).toBe(2)
  })
})
