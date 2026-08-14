import { describe, expect, it } from 'vitest'
import { seededRng } from '../../src/generate/rng'
import { GENERATOR_FAMILIES, readKnobs } from '../../src/generate'
import { propShrinkFamily } from '../../src/generate/prop/family'
import { connectiveCount, containsDoubleNegation, isTautology } from '../../src/generate/prop/formula'
import { isMinimalTautology } from '../../src/generate/prop/shrink'
import { parseFormula } from '../../src/formula/parse'
import type { Formula } from '../../src/formula/syntax'
import type { PropFormula } from '../../src/generate/prop/formula'
import { atomName } from '../../src/generate/prop/formula'

function fromParsed(formula: Formula): PropFormula {
  switch (formula.kind) {
    case 'atom': {
      const index = [...Array(64).keys()].find((i) => atomName(i) === formula.name)
      if (index === undefined) throw new Error(`unexpected atom name '${formula.name}'`)
      return { kind: 'atom', index }
    }
    case 'not':
      return { kind: 'not', body: fromParsed(formula.body) }
    case 'and':
      return { kind: 'and', left: fromParsed(formula.left), right: fromParsed(formula.right) }
    default:
      throw new Error(`unexpected connective '${formula.kind}'`)
  }
}

describe('readKnobs', () => {
  it('applies defaults, enforces minima and integrality, rejects unknown keys', () => {
    expect(readKnobs(propShrinkFamily, {})).toEqual({ atoms: 3, sampleSize: 12, minSize: 6, attempts: 10_000 })
    expect(readKnobs(propShrinkFamily, { atoms: 2 }).atoms).toBe(2)
    expect(() => readKnobs(propShrinkFamily, { atoms: 0 })).toThrow(/atoms/)
    expect(() => readKnobs(propShrinkFamily, { atoms: 2.5 })).toThrow(/integer/)
    expect(() => readKnobs(propShrinkFamily, { bogus: 1 })).toThrow(/bogus/)
  })
})

describe('propShrinkFamily', () => {
  it('is registered first', () => {
    expect(GENERATOR_FAMILIES[0]?.id).toBe('prop-shrink')
  })
  it('generates minimal tautologies meeting the size knob, statement parseable and drawable', () => {
    const rng = seededRng(11)
    for (let round = 0; round < 3; round += 1) {
      const problem = propShrinkFamily.generate({ atoms: 2, sampleSize: 9, minSize: 3, attempts: 10_000 }, rng)
      const parsed = parseFormula(problem.statement)
      if (parsed.kind !== 'quantifier') throw new Error('statement is not quantified')
      const body = fromParsed(parsed.body)
      expect(isTautology(body, parsed.binders.length)).toBe(true)
      expect(isMinimalTautology(body, parsed.binders.length)).toBe(true)
      expect(connectiveCount(body)).toBeGreaterThanOrEqual(3)
      expect(containsDoubleNegation(body)).toBe(false)
      expect(problem.diagram.root).toBeDefined()
      expect(problem.walkUpperBound).toBeUndefined()
    }
  })
  it('throws loudly when the knobs are unsatisfiable within the attempt cap', () => {
    // A 1-connective core over 1 atom cannot reach 5 connectives minimum
    // when sampled at size 1 (cores never exceed the sampled size).
    expect(() => propShrinkFamily.generate({ atoms: 1, sampleSize: 1, minSize: 5, attempts: 50 }, seededRng(1)))
      .toThrow(/50 attempts/)
  })
})
