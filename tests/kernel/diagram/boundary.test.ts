import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { boundaryArity, mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { dwbFromJson, dwbToJson } from '../../../src/kernel/proof/json'
import { parseTerm } from '../../../src/kernel/term/parse'

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
})

describe('DiagramWithBoundary root-open invariant', () => {
  it('rejects a boundary wire scoped below the diagram root at construction', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const nested = b.wire(cut, [])

    expect(() => mkDiagramWithBoundary(b.build(), [nested]))
      .toThrowError(/boundary wire.*must be scoped at the diagram root/i)
  })

  it('rejects a nested boundary wire during strict JSON reconstruction', () => {
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const nested = b.wire(cut, [])
    const serialized = dwbToJson(mkDiagramWithBoundary(b.build(), [])) as { diagram: unknown }

    expect(() => dwbFromJson({
      diagram: serialized.diagram,
      boundary: [nested],
    }, 'nested pattern')).toThrowError(/nested pattern.*boundary wire.*diagram root/i)
  })

  it('preserves repeated ordered occurrences of a root-scoped boundary wire', () => {
    const b = new DiagramBuilder()
    const rootWire = b.wire(b.root, [])

    expect(mkDiagramWithBoundary(b.build(), [rootWire, rootWire]).boundary)
      .toEqual([rootWire, rootWire])
  })
})
