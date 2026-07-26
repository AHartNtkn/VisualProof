import { describe, expect, it } from 'vitest'
import { planCopy } from '../../src/app/copy-planner'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { UNARY } from '../fixtures/zero-signature'

describe('copy interaction handoff', () => {
  it('carries a finite placement point with an edit plan', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root, regions: [], nodes: [node], wires: [],
    })
    const plan = planCopy(diagram, selection, {
      kind: 'edit',
      diagram,
      region: diagram.root,
      at: { x: 8, y: 13 },
    })
    expect(plan).toMatchObject({ kind: 'edit', at: { x: 8, y: 13 } })
  })
})
