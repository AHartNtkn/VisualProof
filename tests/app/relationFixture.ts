import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { unaryDefinition } from '../fixtures/zero-signature'

export const emptyCtx = EMPTY_PROOF_CONTEXT

export function sheetBody() {
  const definition = unaryDefinition()
  const atom = Object.keys(definition.diagram.nodes)[0]!
  const argument = definition.boundary[0]!
  const selection = mkSelection(definition.diagram, {
    region: definition.diagram.root,
    regions: [],
    nodes: [atom],
    wires: [],
  })
  return {
    d: definition.diagram,
    sel: selection,
    atom,
    argument,
  }
}
