import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../../src/kernel/term/parse'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary, boundaryArity } from '../../../src/kernel/diagram/boundary'

const noConsts = new Set<string>()
const p = (s: string) => parseTerm(s, noConsts)

describe('mkDiagramWithBoundary', () => {
  it('accepts ordered boundary wires and reports arity; a relation IS a diagram with a boundary', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. y x'))
    const w0 = b.wire(b.root, [{ node: t, port: { kind: 'output' } }])
    const w1 = b.wire(b.root, [{ node: t, port: { kind: 'freeVar', name: 'y' } }])
    const d = b.build()
    const rel = mkDiagramWithBoundary(d, [w0, w1])
    expect(boundaryArity(rel)).toBe(2)
    expect(rel.boundary).toEqual(['w0', 'w1'])
  })

  it('accepts an empty boundary (a sentence is a 0-ary relation)', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    const rel = mkDiagramWithBoundary(b.build(), [])
    expect(boundaryArity(rel)).toBe(0)
  })

  it('rejects boundary wires that do not exist', () => {
    const b = new DiagramBuilder()
    b.termNode(b.root, p('\\x. x'))
    expect(() => mkDiagramWithBoundary(b.build(), ['ghost']))
      .toThrowError(/boundary wire 'ghost' does not exist/)
  })

  it('rejects duplicate boundary wires', () => {
    const b = new DiagramBuilder()
    const t = b.termNode(b.root, p('\\x. x'))
    const w = b.wire(b.root, [{ node: t, port: { kind: 'output' } }])
    expect(() => mkDiagramWithBoundary(b.build(), [w, w]))
      .toThrowError(/duplicate boundary wire 'w0'/)
  })
})
