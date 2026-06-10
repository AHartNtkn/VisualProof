import { describe, it, expect } from 'vitest'
import { mkDiagram, type Region } from '../../../src/kernel/diagram/diagram'
import { isAncestorOrEqual, cutDepth, polarity } from '../../../src/kernel/diagram/regions'

// sheet > cut1 > bubble > cut2 ; sheet > bubble2
const regions: Record<string, Region> = {
  r0: { kind: 'sheet' },
  r1: { kind: 'cut', parent: 'r0' },
  r2: { kind: 'bubble', parent: 'r1', arity: 1 },
  r3: { kind: 'cut', parent: 'r2' },
  r4: { kind: 'bubble', parent: 'r0', arity: 0 },
}
const d = mkDiagram({ root: 'r0', regions })

describe('isAncestorOrEqual', () => {
  it('is reflexive and follows the parent chain', () => {
    expect(isAncestorOrEqual(d, 'r0', 'r0')).toBe(true)
    expect(isAncestorOrEqual(d, 'r0', 'r3')).toBe(true)
    expect(isAncestorOrEqual(d, 'r1', 'r3')).toBe(true)
    expect(isAncestorOrEqual(d, 'r3', 'r1')).toBe(false)
    expect(isAncestorOrEqual(d, 'r4', 'r3')).toBe(false)
  })

  it('throws on unknown region ids', () => {
    expect(() => isAncestorOrEqual(d, 'ghost', 'r0')).toThrowError(/unknown region 'ghost'/)
    expect(() => isAncestorOrEqual(d, 'r0', 'ghost')).toThrowError(/unknown region 'ghost'/)
    expect(() => isAncestorOrEqual(d, 'ghost', 'ghost')).toThrowError(/unknown region 'ghost'/)
  })
})

describe('cutDepth and polarity', () => {
  it('counts cuts on the path from root, inclusive; bubbles do not count', () => {
    expect(cutDepth(d, 'r0')).toBe(0)
    expect(cutDepth(d, 'r1')).toBe(1)
    expect(cutDepth(d, 'r2')).toBe(1) // bubble does not add
    expect(cutDepth(d, 'r3')).toBe(2)
    expect(cutDepth(d, 'r4')).toBe(0)
  })

  it('polarity is positive iff cut depth is even — bubbles never flip it', () => {
    expect(polarity(d, 'r0')).toBe('positive')
    expect(polarity(d, 'r1')).toBe('negative')
    expect(polarity(d, 'r2')).toBe('negative')
    expect(polarity(d, 'r3')).toBe('positive')
    expect(polarity(d, 'r4')).toBe('positive')
  })

  it('throws on unknown region ids', () => {
    expect(() => cutDepth(d, 'ghost')).toThrowError(/unknown region 'ghost'/)
    expect(() => polarity(d, 'ghost')).toThrowError(/unknown region 'ghost'/)
  })
})
