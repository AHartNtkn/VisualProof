import { describe, expect, it } from 'vitest'
import {
  EMPTY_PROOF_CONTEXT,
  applyStep,
  verifyTheory,
} from '../../../src/kernel/proof/index'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'

describe('fresh public proof barrel import', () => {
  it('initializes the empty authority, verifier, and dispatcher without a module cycle failure', () => {
    expect(verifyTheory({ relations: {}, theorems: [] })).toBe(EMPTY_PROOF_CONTEXT)
    const diagram = new DiagramBuilder().build()
    expect(() => applyStep(diagram, {
      rule: 'doubleCutIntro',
      sel: { region: diagram.root, regions: [], nodes: [], wires: [] },
    }, EMPTY_PROOF_CONTEXT)).not.toThrow()
  })
})
