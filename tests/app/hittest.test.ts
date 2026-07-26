import { describe, expect, it } from 'vitest'
import { buildSelection } from '../../src/app/hit-selection'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { UNARY } from '../fixtures/zero-signature'

describe('hit selection policy', () => {
  it('anchors structural hits in one direct region', () => {
    const builder = new DiagramBuilder()
    const node = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const cut = builder.cut(builder.root)
    const diagram = builder.build()
    expect(buildSelection(diagram, [
      { kind: 'node', id: node },
      { kind: 'region', id: cut },
    ])).toMatchObject({
      region: diagram.root,
      nodes: [node],
      regions: [cut],
    })
  })

  it('rejects cross-region reaches', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const inner = builder.ref(cut, 'UnaryWitness', UNARY)
    const outer = builder.ref(builder.root, 'UnaryWitness', UNARY)
    const diagram = builder.build()
    expect(() => buildSelection(diagram, [
      { kind: 'node', id: inner },
      { kind: 'node', id: outer },
    ])).toThrow(/spans several regions/)
  })
})
