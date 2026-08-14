import { describe, expect, it } from 'vitest'
import { formulaToDiagram } from '../../src/formula'
import { sameDiagram } from '../../src/kernel/diagram'
import { printTheorem, usedAtoms } from '../../src/generate/prop/formula'
import { readPropTheorem } from '../../src/generate/prop/read'

const STATEMENTS = [
  '∀P:o. ¬(P ∧ ¬P)',
  '∀P Q:o. ¬(¬(P ∧ Q) ∧ P ∧ Q)',
  '∀P Q:o. ¬(P ∧ ¬P) ∧ ¬(Q ∧ ¬Q)',
  '∀P:o. ¬¬¬(P ∧ ¬P)',
]

describe('readPropTheorem', () => {
  it('round-trips statements through the formula pipeline up to isomorphism', () => {
    for (const statement of STATEMENTS) {
      const diagram = formulaToDiagram(statement)
      const reading = readPropTheorem(diagram)
      expect(usedAtoms(reading.formula).size).toBe(reading.wires.length)
      const reprinted = printTheorem(reading.formula)
      expect(sameDiagram(formulaToDiagram(reprinted), diagram)).toBe(true)
    }
  })
  it('rejects diagrams outside the propositional ∀-shell fragment', () => {
    // No shell at all: a bare noncontradiction over an unquantified shape.
    expect(() => readPropTheorem(formulaToDiagram('∀x:i. ∀Z:i→o. ¬(Z(x) ∧ ¬Z(x))')))
      .toThrow(/readPropTheorem/)
  })
})
