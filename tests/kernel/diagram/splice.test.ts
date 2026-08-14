import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram, type Region } from '../../../src/kernel/diagram/diagram'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyIdentification } from '../../../src/kernel/rules/identity-rules'
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

    expect(sameDiagram(spliced.diagram, value.diagram)).toBe(true)
    expect(spliced.wireMap.get(extraction.pattern.boundary[0]!)).toBe(value.shared)
  })

  it('records a co-scoped repeated boundary as an identity that identification can collapse', () => {
    const hostDiagram = bareHost()
    const spliced = spliceSubgraphMapped(
      hostDiagram,
      hostDiagram.root,
      repeatedBareBoundary(),
      ['b', 'a'],
    )

    // Splice states the equality the repeated boundary position asserts; it
    // does not act on it.
    expect(spliced.diagram.nodes.identity_0).toEqual({
      kind: 'identity',
      region: 'r0',
      sig: IOTA,
      arity: 2,
    })
    expect(Object.keys(spliced.diagram.wires).sort()).toEqual(['a', 'b'])
    // The stub lands on the wire its FIRST boundary position names; the
    // second position becomes the identity's other port.
    expect(spliced.wireMap.get('stub')).toBe('b')

    // Co-scoped is exactly the configuration the one-point rule needs: both
    // lines are quantified at the region where they are equated.
    const collapsed = applyIdentification(spliced.diagram, {
      kind: 'collapse',
      node: 'identity_0',
      survivor: 'a',
      absorbed: ['b'],
    })
    expect(Object.keys(collapsed.wires)).toEqual(['a'])
    expect(derivedScope(collapsed, 'a')).toBe('r0')
  })

  it('receipts every mint, the alias identity among them', () => {
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
    const pattern = patternBuilder.buildOpen([boundary, boundary])
    const hostDiagram = bareHost()

    const spliced = spliceSubgraphMapped(
      hostDiagram,
      hostDiagram.root,
      pattern,
      ['b', 'a'],
    )

    // The receipt lists every id the splice minted: the copied atom, the pin
    // completing its head wire, and the identity aliasing the two boundary
    // positions. Nothing is minted and then quietly withdrawn, so every id on
    // the receipt is present in the result.
    expect(spliced.allocation).toEqual({
      regions: ['r1'],
      nodes: ['n0', 'n1', 'identity_0'],
      wires: ['w1'],
    })
    for (const id of spliced.allocation.nodes) {
      expect(spliced.diagram.nodes[id]).toBeDefined()
    }
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

    // Both lines are quantified outside the region where the splice equates
    // them, so absorbing either would move a quantifier inward — join/sever's
    // gated business, not the one-point rule's.
    expect(() => applyIdentification(spliced.diagram, {
      kind: 'collapse',
      node: identities[0]![0],
      survivor: 'a',
      absorbed: ['b'],
    })).toThrowError(/quantifier does not sit where it is equated/)
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
