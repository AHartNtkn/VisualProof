import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import {
  boundaryArity,
  mkDiagramWithBoundary,
} from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

describe('DiagramWithBoundary', () => {
  it('preserves ordered incidences including repeated wire ids', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'Pair', relSig([IOTA, IOTA]))
    const left = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const right = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const bounded = mkDiagramWithBoundary(builder.build(), [right, left, right])

    expect(bounded.boundary).toEqual([right, left, right])
    expect(boundaryArity(bounded)).toBe(3)
    expect(Object.isFrozen(bounded.boundary)).toBe(true)
  })

  it('rejects missing and non-root-scoped boundary wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const ref = builder.ref(cut, 'P', relSig([IOTA]))
    const inner = builder.wire( [
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => mkDiagramWithBoundary(diagram, ['ghost']))
      .toThrowError(/does not exist/)
    expect(() => mkDiagramWithBoundary(diagram, [inner]))
      .toThrowError(/must be scoped at the diagram root/)
  })
})
