import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { verifyTheory } from '../../src/kernel/proof/context'
import { unaryDefinition, tinyTheory } from '../fixtures/zero-signature'

describe('proof-context authority', () => {
  it('uses only the supplied verified relation and theorem stores', () => {
    const definition = unaryDefinition()
    const node = Object.keys(definition.diagram.nodes)[0]!
    const selection = mkSelection(definition.diagram, {
      region: definition.diagram.root, regions: [], nodes: [node], wires: [],
    })
    const actions = applicableActions(
      definition.diagram,
      selection,
      verifyTheory(tinyTheory()),
    )
    expect(actions.some((action) => action.kind === 'relFold')).toBe(true)
    expect(actions.some((action) =>
      action.kind === 'citeTheorem' && action.name === 'StructuralReflexivity')).toBe(true)
  })
})
