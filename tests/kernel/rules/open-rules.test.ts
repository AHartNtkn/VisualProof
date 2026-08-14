import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import {
  applyDeiteration,
  applyIteration,
  findDeiterationEvidence,
} from '../../../src/kernel/rules/iteration'

function host() {
  const builder = new DiagramBuilder()
  const outer = builder.cut(builder.root)
  const atom = builder.atom(outer, relSig([IOTA]))
  const argument = builder.wire( [
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const target = builder.cut(outer)
  return { diagram: builder.build(), outer, atom, argument, target }
}

describe('open relational iteration and deiteration', () => {
  it('copies an atom with ordinary argument and relational-head attachments, then removes it exactly', () => {
    const { diagram, outer, atom, argument, target } = host()
    const selection = mkSelection(diagram, {
      region: outer,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    const iterated = applyIteration(diagram, selection, target)
    const copy = Object.entries(iterated.nodes)
      .find(([id, node]) => id !== atom && node.kind === 'atom' && node.region === target)![0]
    const copySelection = mkSelection(iterated, {
      region: target,
      regions: [],
      nodes: [copy],
      wires: [],
    })
    const evidence = findDeiterationEvidence(iterated, copySelection, 10_000)
    const restored = applyDeiteration(
      iterated,
      copySelection,
      evidence.justifier,
      evidence.certificate,
    )

    expect(iterated.wires[argument]!.endpoints.some((endpoint) => endpoint.node === copy))
      .toBe(true)
    expect(sameDiagram(restored, diagram)).toBe(true)
  })

  it('rejects iteration to a region outside the source', () => {
    const { diagram, outer, atom } = host()
    const selection = mkSelection(diagram, {
      region: outer,
      regions: [],
      nodes: [atom],
      wires: [],
    })

    expect(() => applyIteration(diagram, selection, diagram.root))
      .toThrowError(/must lie within the source region/)
  })

  it('requires the same relational head attachment, not only atom signature and arguments', () => {
    const builder = new DiagramBuilder()
    const first = builder.atom(builder.root, relSig([IOTA]))
    const second = builder.atom(builder.root, relSig([IOTA]))
    builder.wire( [
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

    expect(() => findDeiterationEvidence(diagram, selection, 10_000))
      .toThrowError(/no exact justifying occurrence/)
  })
})
