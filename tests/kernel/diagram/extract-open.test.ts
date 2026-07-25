import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig, sigEquals } from '../../../src/kernel/diagram/sig'
import { extractSubgraph } from '../../../src/kernel/diagram/subgraph/extract'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'

describe('extraction with open signature-indexed lines', () => {
  it('turns an externally scoped atom head into a typed boundary stub', () => {
    const relation = relSig([IOTA])
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relation)
    const head = builder.wire(
      builder.root,
      [{ node: atom, port: { kind: 'head' } }],
      relation,
    )
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    })
    const extraction = extractSubgraph(diagram, selection)
    const stub = extraction.pattern.diagram.wires[extraction.pattern.boundary[0]!]!

    expect(extraction.attachments).toEqual([head])
    expect(stub.scope).toBe(extraction.pattern.diagram.root)
    expect(sigEquals(stub.sig, relation)).toBe(true)
    expect(stub.endpoints).toEqual([{ node: atom, port: { kind: 'head' } }])
    expect(() => mkDiagram({
      root: extraction.pattern.diagram.root,
      regions: { ...extraction.pattern.diagram.regions },
      nodes: { ...extraction.pattern.diagram.nodes },
      wires: { ...extraction.pattern.diagram.wires },
    })).not.toThrow()
  })

  it('keeps a fully internal extraction closed', () => {
    const relation = relSig([])
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relation)
    builder.wire(cut, [{ node: atom, port: { kind: 'head' } }], relation)
    const diagram = builder.build()
    const extraction = extractSubgraph(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    }))

    expect(extraction.attachments).toEqual([])
    expect(extraction.pattern.boundary).toEqual([])
  })

  it('orders multiple relational stubs deterministically by host wire id', () => {
    const unary = relSig([IOTA])
    const nullary = relSig([])
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const unaryAtom = builder.atom(cut, unary)
    const nullaryAtom = builder.atom(cut, nullary)
    builder.wire(
      builder.root,
      [{ node: unaryAtom, port: { kind: 'head' } }],
      unary,
    )
    builder.wire(
      builder.root,
      [{ node: nullaryAtom, port: { kind: 'head' } }],
      nullary,
    )
    const diagram = builder.build()
    const extraction = extractSubgraph(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    }))

    expect(extraction.attachments).toEqual([...extraction.attachments].sort())
    expect(extraction.pattern.boundary).toHaveLength(2)
    const signatures = extraction.pattern.boundary.map(
      (wire) => extraction.pattern.diagram.wires[wire]!.sig,
    )
    expect(signatures.some((sig) => sigEquals(sig, unary))).toBe(true)
    expect(signatures.some((sig) => sigEquals(sig, nullary))).toBe(true)
  })

  it('treats a crossing argument wire exactly like a crossing head wire', () => {
    const relation = relSig([IOTA])
    const builder = new DiagramBuilder()
    const outside = builder.ref(builder.root, 'Outside', relSig([IOTA]))
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, relation)
    builder.wire(cut, [{ node: atom, port: { kind: 'head' } }], relation)
    const crossing = builder.wire(builder.root, [
      { node: outside, port: { kind: 'arg', index: 0 } },
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const extraction = extractSubgraph(diagram, mkSelection(diagram, {
      region: diagram.root,
      regions: [cut],
      nodes: [],
      wires: [],
    }))

    expect(extraction.attachments).toEqual([crossing])
    const stub = extraction.pattern.diagram.wires[extraction.pattern.boundary[0]!]!
    expect(stub.scope).toBe(extraction.pattern.diagram.root)
    expect(sigEquals(stub.sig, IOTA)).toBe(true)
  })
})
