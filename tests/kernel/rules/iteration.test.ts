import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'
import { contentEndpoints } from '../../fixtures/pins'

function host() {
  const builder = new DiagramBuilder()
  const node = builder.ref(builder.root, 'P', relSig([IOTA]))
  const wire = builder.wire([
    { node, port: { kind: 'arg', index: 0 } },
  ])
  const cut = builder.cut(builder.root)
  return { diagram: builder.build(), node, wire, cut }
}

function rootAtomWithWire() {
  const builder = new DiagramBuilder()
  const node = builder.atom(builder.root, relSig([IOTA]))
  const wire = builder.wire([
    { node, port: { kind: 'arg', index: 0 } },
  ])
  return { diagram: builder.build(), node, wire }
}

function deiterate(
  diagram: Parameters<typeof applyDeiteration>[0],
  selection: Parameters<typeof applyDeiteration>[1],
  explorationFuel = 10_000,
) {
  const evidence = findDeiterationEvidence(diagram, selection, explorationFuel)
  return applyDeiteration(
    diagram,
    selection,
    evidence.justifier,
    evidence.certificate,
  )
}

describe('applyIteration', () => {
  it('keeps an explicitly selected root wire distinct from the copied atom wire', () => {
    const { diagram, node, wire } = rootAtomWithWire()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [wire],
    })

    const iterated = applyIteration(diagram, selection, diagram.root)

    expect(derivedScope(iterated, wire)).toBe(diagram.root)
    expect(contentEndpoints(iterated, wire)).toEqual([
      { node, port: { kind: 'arg', index: 0 } },
    ])

    const copiedNode = Object.entries(iterated.nodes).find(
      ([id, candidate]) =>
        id !== node
        && candidate.kind === 'atom'
        && candidate.region === diagram.root,
    )
    expect(copiedNode).toBeDefined()
    const copiedWire = Object.entries(iterated.wires).find(
      ([id, candidate]) =>
        id !== wire
        && derivedScope(iterated, id) === diagram.root
        && candidate.endpoints.some(
          (endpoint) =>
            endpoint.node === copiedNode![0]
            && endpoint.port.kind === 'arg'
            && endpoint.port.index === 0,
        ),
    )
    expect(copiedWire).toBeDefined()
    expect(copiedWire![0]).not.toBe(wire)
  })

  it('copies an exact subgraph into a descendant region with shared attachments', () => {
    const { diagram, node, wire, cut } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    const iterated = applyIteration(diagram, selection, cut)

    expect(contentEndpoints(iterated, wire)).toHaveLength(2)
    expect(Object.values(iterated.nodes).filter((candidate) => candidate.region === cut))
      .toHaveLength(1)
  })

  it('permits iteration into the same region', () => {
    const { diagram, node, wire } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    const iterated = applyIteration(diagram, selection, diagram.root)

    expect(contentEndpoints(iterated, wire)).toHaveLength(2)
  })

  it('threads reservations into the splice allocator after retarget evidence', () => {
    const { diagram, node, cut } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    const iterated = applyIteration(diagram, selection, cut, {
      regions: new Set(),
      nodes: new Set([`${node}_0`]),
      wires: new Set(),
    })

    expect(iterated.nodes[`${node}_1`]).toBeDefined()
  })

  it('rejects targets outside the source region and targets inside the copy', () => {
    const builder = new DiagramBuilder()
    const source = builder.cut(builder.root)
    const inner = builder.cut(source)
    const sibling = builder.cut(builder.root)
    const node = builder.ref(source, 'P', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: source,
      regions: [inner],
      nodes: [node],
      wires: [],
    })

    expect(() => applyIteration(diagram, selection, sibling))
      .toThrowError(/must lie within the source region/)
    expect(() => applyIteration(diagram, selection, inner))
      .toThrowError(/lies inside the iterated subgraph/)
  })
})

describe('exact applyDeiteration evidence', () => {
  it('round-trips an iteration by canonical fingerprint', () => {
    const { diagram, node, cut } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })
    const iterated = applyIteration(diagram, selection, cut)
    const copy = Object.entries(iterated.nodes)
      .find(([id, candidate]) => id !== node && candidate.region === cut)![0]
    const copySelection = mkSelection(iterated, {
      region: cut,
      regions: [],
      nodes: [copy],
      wires: [],
    })

    expect(exploreForm(deiterate(iterated, copySelection))).toBe(exploreForm(diagram))
  })

  it('rejects removal with no disjoint exact justifier', () => {
    const { diagram, node } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    expect(() => deiterate(diagram, selection))
      .toThrowError(/no exact justifying occurrence/)
  })

  it('rejects justification from a strict descendant', () => {
    const builder = new DiagramBuilder()
    const outer = builder.ref(builder.root, 'P', relSig([IOTA]))
    const cut = builder.cut(builder.root)
    const inner = builder.ref(cut, 'P', relSig([IOTA]))
    builder.wire([
      { node: outer, port: { kind: 'arg', index: 0 } },
      { node: inner, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [outer],
      wires: [],
    })

    expect(() => deiterate(diagram, selection))
      .toThrowError(/no exact justifying occurrence/)
  })

  it('does not let a copy justify itself or a separately wired isomorph justify removal', () => {
    const singletonBuilder = new DiagramBuilder()
    const singleton = singletonBuilder.ref(singletonBuilder.root, 'P', relSig([]))
    const singletonDiagram = singletonBuilder.build()
    const singletonSelection = mkSelection(singletonDiagram, {
      region: singletonDiagram.root,
      regions: [],
      nodes: [singleton],
      wires: [],
    })
    expect(() => deiterate(singletonDiagram, singletonSelection))
      .toThrowError(/no exact justifying occurrence/)

    const separateBuilder = new DiagramBuilder()
    const first = separateBuilder.ref(separateBuilder.root, 'P', relSig([IOTA]))
    const second = separateBuilder.ref(separateBuilder.root, 'P', relSig([IOTA]))
    separateBuilder.wire([
      { node: first, port: { kind: 'arg', index: 0 } },
    ])
    separateBuilder.wire([
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const separateDiagram = separateBuilder.build()
    const separateSelection = mkSelection(separateDiagram, {
      region: separateDiagram.root,
      regions: [],
      nodes: [second],
      wires: [],
    })
    expect(() => deiterate(separateDiagram, separateSelection))
      .toThrowError(/no exact justifying occurrence/)
  })

  it('removes an attachment-sharing duplicate', () => {
    const builder = new DiagramBuilder()
    const first = builder.ref(builder.root, 'P', relSig([IOTA]))
    const second = builder.ref(builder.root, 'P', relSig([IOTA]))
    builder.wire([
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [second],
      wires: [],
    })

    const result = deiterate(diagram, selection)

    expect(Object.entries(result.nodes)
      .filter(([, node]) => !(node.kind === 'identity' && node.arity === 1))
      .map(([id]) => id)).toEqual([first])
  })

  it('requires exact reference identity, not signature-only isomorphism', () => {
    const builder = new DiagramBuilder()
    const first = builder.ref(builder.root, 'P', relSig([IOTA]))
    const second = builder.ref(builder.root, 'Q', relSig([IOTA]))
    builder.wire([
      { node: first, port: { kind: 'arg', index: 0 } },
      { node: second, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [second],
      wires: [],
    })

    expect(() => deiterate(diagram, selection))
      .toThrowError(/no exact justifying occurrence/)
  })

  it('reports exhausted graph exploration without a semantic undecided channel', () => {
    const { diagram, node } = host()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [node],
      wires: [],
    })

    expect(() => findDeiterationEvidence(diagram, selection, 1))
      .toThrowError(/graph exploration exhausted/)
  })
})
