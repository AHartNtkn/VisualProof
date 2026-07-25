import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagram } from '../../../src/kernel/diagram/diagram'
import { boundaryArity, mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { parseTerm } from '../../../src/kernel/term/parse'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

const p = (source: string) => parseTerm(source)

describe('mkDiagramWithBoundary', () => {
  it('accepts ordered boundary wires and reports arity; a relation is a diagram with a boundary', () => {
    const b = new DiagramBuilder()
    const term = b.termNode(b.root, p('\\x. y x'))
    const output = b.wire(b.root, [{ node: term, port: { kind: 'output' } }])
    const free = b.wire(b.root, [{ node: term, port: { kind: 'freeVar', name: 'y' } }])
    const relation = mkDiagramWithBoundary(b.build(), [output, free])

    expect(boundaryArity(relation)).toBe(2)
    expect(relation.boundary).toEqual([output, free])
  })

  it('accepts an empty boundary', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))

    expect(boundaryArity(mkDiagramWithBoundary(b.build(), []))).toBe(0)
  })

  it('rejects boundary wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))

    expect(() => mkDiagramWithBoundary(b.build(), ['ghost']))
      .toThrowError(/boundary wire 'ghost' does not exist/)
  })

  it('accepts a boundary wire of relational sig — the boundary is sort-agnostic', () => {
    const b = new DiagramBuilder()
    const sig = relSig([IOTA, IOTA])
    const a = b.atom(b.root, sig)
    const head = b.wire(b.root, [{ node: a, port: { kind: 'head' } }], sig)
    const relation = mkDiagramWithBoundary(b.build(), [head])

    expect(boundaryArity(relation)).toBe(1)
    expect(relation.diagram.wires[head]!.sig).toEqual(sig)
  })
})

describe('DiagramWithBoundary root-open invariant', () => {
  it('rejects a boundary wire scoped below the diagram root at construction', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const nested = b.wire(cut, [])

    expect(() => mkDiagramWithBoundary(b.build(), [nested]))
      .toThrowError(/boundary wire.*must be scoped at the diagram root/i)
  })

  it('rejects a nested boundary wire on a Diagram value reconstructed independently of the builder', () => {
    // The invariant must hold for any Diagram, not merely ones produced
    // through DiagramBuilder's convenience layer — e.g. a value rebuilt from
    // an external representation (JSON, a copy transform, …) that happens to
    // carry the identical regions/nodes/wires.
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const nested = b.wire(cut, [])
    const built = b.build()
    const reconstructed = mkDiagram({
      root: built.root,
      regions: { ...built.regions },
      nodes: { ...built.nodes },
      wires: { ...built.wires },
    })

    expect(() => mkDiagramWithBoundary(reconstructed, [nested]))
      .toThrowError(/boundary wire.*must be scoped at the diagram root/i)
  })

  it('preserves repeated ordered occurrences of a root-scoped boundary wire', () => {
    const b = new DiagramBuilder()
    const rootWire = b.wire(b.root, [])

    expect(mkDiagramWithBoundary(b.build(), [rootWire, rootWire]).boundary)
      .toEqual([rootWire, rootWire])
  })
})
