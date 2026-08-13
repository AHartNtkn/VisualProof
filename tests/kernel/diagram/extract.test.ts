import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'

function host() {
  const builder = new DiagramBuilder()
  const outer = builder.ref(builder.root, 'Outer', relSig([IOTA]))
  const cut = builder.cut(builder.root)
  const inner = builder.ref(cut, 'Inner', relSig([IOTA, IOTA]))
  const shared = builder.wire( [
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
  ])
  const inside = builder.wire( [
    { node: inner, port: { kind: 'arg', index: 1 } },
  ])
  return {
    diagram: builder.build(),
    outer,
    cut,
    inner,
    shared,
    inside,
  }
}

describe('extractSubgraph', () => {
  it('copies a selected subtree and exposes crossings as ordered root stubs', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [],
      wires: [],
    })
    const extraction = extractSubgraph(value.diagram, selection)
    const boundary = extraction.pattern.boundary[0]!
    const pattern = extraction.pattern.diagram

    expect(extraction.attachments).toEqual([value.shared])
    expect(pattern.nodes[value.inner]).toEqual(value.diagram.nodes[value.inner])
    expect(pattern.wires[value.inside]?.scope).toBe(value.cut)
    expect(pattern.wires[boundary]?.scope).toBe(pattern.root)
    expect(pattern.wires[boundary]?.endpoints).toEqual([
      { node: value.inner, port: { kind: 'arg', index: 0 } },
    ])
  })

  it('moves directly selected nodes to the fresh pattern root', () => {
    const value = host()
    const extraction = extractSubgraph(value.diagram, mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [],
      nodes: [value.outer],
      wires: [],
    }))

    expect(extraction.pattern.diagram.nodes[value.outer]?.region)
      .toBe(extraction.pattern.diagram.root)
    expect(extraction.attachments).toEqual([value.shared])
  })

  it('is deterministic and non-destructive', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [],
      wires: [],
    })
    const first = extractSubgraph(value.diagram, selection)
    const second = extractSubgraph(value.diagram, selection)

    expect(first).toEqual(second)
    expect(value.diagram.nodes[value.inner]?.region).toBe(value.cut)
  })

  it('preserves a selected conditional identity across distinct bounded attachments', () => {
    const diagram = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      nodes: {
        eq: { kind: 'identity', region: 'r1', sig: IOTA, arity: 2 },
      },
      wires: {
        a: {
          scope: 'r0',
          sig: IOTA,
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 0 } }],
        },
        b: {
          scope: 'r0',
          sig: IOTA,
          endpoints: [{ node: 'eq', port: { kind: 'identity', index: 1 } }],
        },
      },
    })
    const extraction = extractSubgraph(diagram, mkSelection(diagram, {
      region: 'r1',
      regions: [],
      nodes: ['eq'],
      wires: [],
    }))

    expect(extraction.pattern.diagram.nodes.eq).toEqual({
      kind: 'identity',
      region: extraction.pattern.diagram.root,
      sig: IOTA,
      arity: 2,
    })
    expect(extraction.pattern.boundary[0]).not.toBe(extraction.pattern.boundary[1])
    expect(extraction.pattern.diagram.wires[extraction.pattern.boundary[0]!]!.endpoints)
      .toEqual([{ node: 'eq', port: { kind: 'identity', index: 0 } }])
    expect(extraction.pattern.diagram.wires[extraction.pattern.boundary[1]!]!.endpoints)
      .toEqual([{ node: 'eq', port: { kind: 'identity', index: 1 } }])
    expect(extraction.attachments).toEqual(['a', 'b'])
  })
})
