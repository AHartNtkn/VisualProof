import { describe, expect, it } from 'vitest'
import { applicableActions } from '../../src/app/actions'
import { proofConnectionStep } from '../../src/app/interact/moves'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../src/kernel/diagram/sig'
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
    expect(kinds).not.toContain('relationJoin')
    expect(kinds).not.toContain('relationSever')
  })

  it('constructs direct connection drags only as durable IOTA joins', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], IOTA)
    const right = builder.wire(negative, [], IOTA)
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
  })

  it('builds relation-wire merges through the same connection gesture', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const left = builder.wire(negative, [], relSig([]))
    const right = builder.wire(negative, [], relSig([]))
    const diagram = builder.build()

    expect(proofConnectionStep(
      diagram,
      { wire: left, endpoint: null },
      { wire: right, endpoint: null },
      'forward',
      0,
    )).toEqual({
      rule: 'wireJoin',
      input: { a: left, b: right },
    })
  })

})
