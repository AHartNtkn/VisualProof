import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import {
  boundaryArity,
  mkDiagramWithBoundary,
} from '../../../src/kernel/diagram/boundary'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'

describe('DiagramWithBoundary', () => {
  it('preserves ordered incidences including repeated wire ids', () => {
    const builder = new DiagramBuilder()
    const ref = builder.ref(builder.root, 'Pair', relSig([IOTA, IOTA]))
    const left = builder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const right = builder.wire([
      { node: ref, port: { kind: 'arg', index: 1 } },
    ])
    const bounded = builder.buildOpen([right, left, right])

    expect(bounded.boundary).toEqual([right, left, right])
    expect(boundaryArity(bounded)).toBe(3)
    expect(Object.isFrozen(bounded.boundary)).toBe(true)
  })

  it('rejects missing boundary wires and roots the scope of every wire it exposes', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const ref = builder.ref(cut, 'P', relSig([IOTA]))
    const inner = builder.wire([
      { node: ref, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => mkDiagramWithBoundary(diagram, ['ghost']))
      .toThrowError(/does not exist/)

    // Every endpoint of `inner` sits inside the cut, so it is cut-scoped as
    // an internal wire; exposing it adds a root incidence, which is what
    // makes a boundary wire root-scoped — there is nothing left to reject.
    expect(derivedScope(diagram, inner)).toBe(cut)
    const bounded = mkDiagramWithBoundary(diagram, [inner])
    expect(derivedScope(bounded.diagram, inner, bounded.boundary)).toBe(builder.root)
  })
})
