import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import type { Diagram } from '../../../src/kernel/diagram/diagram'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import {
  mkSelection,
  type SubgraphSelection,
} from '../../../src/kernel/diagram/subgraph/selection'
import {
  removeSubgraph,
  spliceSubgraph,
} from '../../../src/kernel/diagram/subgraph/splice'
import { bareWire } from '../../fixtures/pins'

function roundTrip(diagram: Diagram, rawSelection: SubgraphSelection): void {
  const selection = mkSelection(diagram, rawSelection)
  const extraction = extractSubgraph(diagram, selection)
  const removed = removeSubgraph(diagram, selection)
  const restored = spliceSubgraph(
    removed,
    selection.region,
    extraction.pattern,
    extraction.attachments,
  )
  expect(exploreForm(restored)).toBe(exploreForm(diagram))
}

describe('extract, remove, and splice canonical round trip', () => {
  it('holds for a cut subtree with a crossing wire', () => {
    const builder = new DiagramBuilder()
    const outside = builder.ref(builder.root, 'Outside', relSig([IOTA]))
    const cut = builder.cut(builder.root)
    const inside = builder.ref(cut, 'Inside', relSig([IOTA]))
    const crossing = builder.wire([
      { node: outside, port: { kind: 'arg', index: 0 } },
      { node: inside, port: { kind: 'arg', index: 0 } },
    ])
    // The crossing wire outlives the removal of the cut, so it is pinned at
    // its own scope first.
    builder.pin(crossing, builder.root)
    bareWire(builder, cut)
    const diagram = builder.build()

    roundTrip(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    })
  })

  it('holds for an atom with a shared diagonal argument wire', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relSig([IOTA, IOTA]))
    const feeder = builder.ref(cut, 'Feeder', relSig([IOTA]))
    builder.wire([
      { node: feeder, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    roundTrip(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    })
  })

  it('holds for a mixed direct-node, subtree, and explicit-wire selection', () => {
    const builder = new DiagramBuilder()
    const direct = builder.ref(builder.root, 'Direct', relSig([IOTA]))
    const cut = builder.cut(builder.root)
    const nested = builder.ref(cut, 'Nested', relSig([IOTA]))
    const wire = builder.wire([
      { node: direct, port: { kind: 'arg', index: 0 } },
      { node: nested, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    roundTrip(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [direct],
      wires: [wire],
    })
  })

  it('holds below the root inside a nested region', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const inner = builder.cut(outer)
    builder.ref(outer, 'Outer', relSig([]))
    builder.ref(inner, 'Inner', relSig([]))
    const diagram = builder.build()

    roundTrip(diagram, {
      region: outer,
      regions: [inner],
      nodes: [],
      wires: [],
    })
  })

  it('holds for the empty selection', () => {
    const builder = new DiagramBuilder()
    builder.ref(builder.root, 'P', relSig([]))
    const diagram = builder.build()

    roundTrip(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    })
  })
})
