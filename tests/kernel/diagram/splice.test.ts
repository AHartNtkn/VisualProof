import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  removeSubgraph,
  spliceSubgraphMapped,
} from '../../../src/kernel/diagram/subgraph/splice'

function host() {
  const builder = new DiagramBuilder()
  const outer = builder.ref(builder.root, 'Outer', relSig([IOTA]))
  const cut = builder.cut(builder.root)
  const inner = builder.ref(cut, 'Inner', relSig([IOTA, IOTA]))
  const shared = builder.wire(builder.root, [
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
  ])
  const inside = builder.wire(cut, [
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

function repeatedBareBoundary() {
  const diagram = mkDiagram({
    root: 'p0',
    regions: { p0: { kind: 'sheet' } },
    wires: {
      stub: { scope: 'p0', sig: IOTA, endpoints: [] },
    },
  })
  return mkDiagramWithBoundary(diagram, ['stub', 'stub'])
}

describe('subgraph removal and splice', () => {
  it('removes selected content and trims touching wires', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [],
      wires: [],
    })
    const removed = removeSubgraph(value.diagram, selection)

    expect(removed.regions[value.cut]).toBeUndefined()
    expect(removed.nodes[value.inner]).toBeUndefined()
    expect(removed.wires[value.inside]).toBeUndefined()
    expect(removed.wires[value.shared]?.endpoints).toEqual([
      { node: value.outer, port: { kind: 'arg', index: 0 } },
    ])
  })

  it('extract → remove → mapped splice round-trips canonically', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [],
      wires: [],
    })
    const extraction = extractSubgraph(value.diagram, selection)
    const removed = removeSubgraph(value.diagram, selection)
    const spliced = spliceSubgraphMapped(
      removed,
      removed.root,
      extraction.pattern,
      extraction.attachments,
    )

    expect(exploreForm(spliced.diagram)).toBe(exploreForm(value.diagram))
    expect(spliced.wireMap.get(extraction.pattern.boundary[0]!)).toBe(value.shared)
  })

  it('collapses a repeated boundary identity when attachments are co-scoped', () => {
    const hostDiagram = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      wires: {
        b: { scope: 'r0', sig: IOTA, endpoints: [] },
        a: { scope: 'r0', sig: IOTA, endpoints: [] },
      },
    })
    const spliced = spliceSubgraphMapped(
      hostDiagram,
      hostDiagram.root,
      repeatedBareBoundary(),
      ['b', 'a'],
    )

    expect(spliced.diagram.nodes).toEqual({})
    expect(Object.keys(spliced.diagram.wires)).toEqual(['a'])
    expect(spliced.wireMap.get('stub')).toBe('a')
  })

  it('receipts every pre-normalization mint even when an alias is normalized away', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const body = patternBuilder.atom(
      patternCut,
      relSig([IOTA]),
    )
    const boundary = patternBuilder.wire(patternBuilder.root, [{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    patternBuilder.wire(patternCut, [{
      node: body,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const pattern = mkDiagramWithBoundary(
      patternBuilder.build(),
      [boundary, boundary],
    )
    const hostDiagram = mkDiagram({
      root: 'r0',
      regions: { r0: { kind: 'sheet' } },
      wires: {
        b: { scope: 'r0', sig: IOTA, endpoints: [] },
        a: { scope: 'r0', sig: IOTA, endpoints: [] },
      },
    })

    const spliced = spliceSubgraphMapped(
      hostDiagram,
      hostDiagram.root,
      pattern,
      ['b', 'a'],
    )

    expect(spliced.allocation).toEqual({
      regions: ['r1'],
      nodes: ['n0', 'identity_0'],
      wires: ['w1'],
    })
    expect(spliced.diagram.nodes.identity_0).toBeUndefined()
    expect(spliced.diagram.nodes.n0).toBeDefined()
    expect(spliced.diagram.wires.w1).toBeDefined()
  })

  it('keeps a repeated-boundary identity for outer-scoped attachments', () => {
    const hostDiagram = mkDiagram({
      root: 'r0',
      regions: {
        r0: { kind: 'sheet' },
        r1: { kind: 'cut', parent: 'r0' },
      },
      wires: {
        a: { scope: 'r0', sig: IOTA, endpoints: [] },
        b: { scope: 'r0', sig: IOTA, endpoints: [] },
      },
    })
    const spliced = spliceSubgraphMapped(
      hostDiagram,
      'r1',
      repeatedBareBoundary(),
      ['a', 'b'],
    )
    const identities = Object.entries(spliced.diagram.nodes)
      .filter(([, node]) => node.kind === 'identity')

    expect(identities).toHaveLength(1)
    expect(identities[0]?.[1]).toMatchObject({
      kind: 'identity',
      region: 'r1',
      sig: IOTA,
      arity: 2,
    })
    expect(Object.keys(spliced.diagram.wires).sort()).toEqual(['a', 'b'])
    expect(spliced.wireMap.get('stub')).toBe('a')
  })

  it('rejects arity, visibility, and signature mismatches', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const innerWire = builder.wire(cut, [])
    const relational = builder.relWire(builder.root, relSig([]))
    const diagram = builder.build()
    const pattern = repeatedBareBoundary()

    expect(() => spliceSubgraphMapped(diagram, cut, pattern, [relational]))
      .toThrowError(/expected 2 attachments/)
    expect(() => spliceSubgraphMapped(diagram, builder.root, pattern, [innerWire, innerWire]))
      .toThrowError(/does not enclose splice region/)
    expect(() => spliceSubgraphMapped(diagram, cut, pattern, [relational, relational]))
      .toThrowError(/cannot land.*sig/)
  })
})
