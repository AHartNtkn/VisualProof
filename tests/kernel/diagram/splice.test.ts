import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram, type Region } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  removeSubgraph,
  spliceSubgraphMapped,
} from '../../../src/kernel/diagram/subgraph/splice'
import { bareWire, bareWireParts, contentEndpoints } from '../../fixtures/pins'

function host() {
  const builder = new DiagramBuilder()
  const outer = builder.ref(builder.root, 'Outer', relSig([IOTA]))
  const cut = builder.cut(builder.root)
  const inner = builder.ref(cut, 'Inner', relSig([IOTA, IOTA]))
  const shared = builder.wire([
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
  ])
  // The wire outlives the removal of the cut, so it is pinned at its own
  // scope first — removal keeps only outside incidences.
  builder.pin(shared, builder.root)
  const inside = builder.wire([
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
  // Two boundary incidences are the stub's two ends, so it needs no pins.
  return mkDiagramWithBoundary({
    root: 'p0',
    regions: { p0: { kind: 'sheet' } },
    nodes: {},
    wires: {
      stub: { sig: IOTA, endpoints: [] },
    },
  }, ['stub', 'stub'])
}

/** A host holding two bare wires, `a` and `b`, at the root. */
function bareHost(regions: Record<string, Region> = {}) {
  const a = bareWireParts('a', 'r0')
  const b = bareWireParts('b', 'r0')
  return mkDiagram({
    root: 'r0',
    regions: { r0: { kind: 'sheet' }, ...regions },
    nodes: { ...a.nodes, ...b.nodes },
    wires: { ...a.wires, ...b.wires },
  })
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
    expect(contentEndpoints(removed, value.shared)).toEqual([
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

  // NEEDS-ADJUDICATION: the identity a repeated boundary creates is no longer
  // absorbed when the attachments are co-scoped — splice records the equality
  // and it persists until an identification step absorbs it.
  it('collapses a repeated boundary identity when attachments are co-scoped', () => {
    const hostDiagram = bareHost()
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

  // NEEDS-ADJUDICATION: the closing assertions expect the minted alias
  // identity to be normalized away. Splice keeps it now, so the receipt and
  // the surviving nodes coincide.
  it('receipts every pre-normalization mint even when an alias is normalized away', () => {
    const patternBuilder = new DiagramBuilder()
    const patternCut = patternBuilder.cut(patternBuilder.root)
    const body = patternBuilder.atom(
      patternCut,
      relSig([IOTA]),
    )
    const boundary = patternBuilder.wire([{
      node: body,
      port: { kind: 'arg', index: 0 },
    }])
    patternBuilder.wire([{
      node: body,
      port: { kind: 'head' },
    }], relSig([IOTA]))
    const pattern = mkDiagramWithBoundary(
      patternBuilder.build(),
      [boundary, boundary],
    )
    const hostDiagram = bareHost()

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
    const hostDiagram = bareHost({ r1: { kind: 'cut', parent: 'r0' } })
    const spliced = spliceSubgraphMapped(
      hostDiagram,
      'r1',
      repeatedBareBoundary(),
      ['a', 'b'],
    )
    const identities = Object.entries(spliced.diagram.nodes)
      .filter(([id, node]) =>
        node.kind === 'identity' && hostDiagram.nodes[id] === undefined)

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
    const innerWire = bareWire(builder, cut)
    const relational = bareWire(builder, builder.root, relSig([]))
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
