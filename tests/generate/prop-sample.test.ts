import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { connectiveCount, usedAtoms, type PropFormula } from '../../src/generate/prop/formula'
import { samplePropFormula } from '../../src/generate/prop/sample'

function assertShape(formula: PropFormula, atoms: number): void {
  switch (formula.kind) {
    case 'atom':
      expect(formula.index).toBeGreaterThanOrEqual(0)
      expect(formula.index).toBeLessThan(atoms)
      return
    case 'not':
      return assertShape(formula.body, atoms)
    case 'and':
      assertShape(formula.left, atoms)
      assertShape(formula.right, atoms)
      return
    default:
      throw new Error(`sampled formula contains forbidden node '${formula.kind}'`)
  }
}

describe('samplePropFormula', () => {
  it('produces exactly the requested connective count over {¬,∧} with in-range atoms', () => {
    const rng = seededRng(7)
    for (let round = 0; round < 200; round += 1) {
      const size = round % 15
      const formula = samplePropFormula(size, 3, rng)
      expect(connectiveCount(formula)).toBe(size)
      assertShape(formula, 3)
    }
  })
  it('is deterministic under a fixed seed', () => {
    expect(samplePropFormula(10, 2, seededRng(99))).toEqual(samplePropFormula(10, 2, seededRng(99)))
  })
  it('exercises the whole alphabet across draws', () => {
    const rng = seededRng(3)
    const seen = new Set<number>()
    for (let round = 0; round < 100; round += 1) {
      for (const atom of usedAtoms(samplePropFormula(6, 4, rng))) seen.add(atom)
    }
    expect([...seen].sort()).toEqual([0, 1, 2, 3])
  })
  it('rejects invalid parameters loudly', () => {
    expect(() => samplePropFormula(-1, 2, seededRng(1))).toThrow(/size/)
    expect(() => samplePropFormula(3, 0, seededRng(1))).toThrow(/atoms/)
  })
})
