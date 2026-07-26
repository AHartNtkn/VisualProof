import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { EMPTY_PROOF_CONTEXT } from '../../src/kernel/proof/context'
import { UNARY } from '../fixtures/zero-signature'

describe('proof move vocabulary', () => {
  it('discovers only structural descriptors', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'Unknown', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const kinds = applicableActions(diagram, selection, EMPTY_PROOF_CONTEXT)
      .map((action) => action.kind)
    expect(kinds).toContain('erase')
    expect(kinds).toContain('iterate')
    expect(kinds).not.toContain('convert')
    expect(kinds).not.toContain('instantiate')
    expect(kinds).not.toContain('abstract')
  })
})
