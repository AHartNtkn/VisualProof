import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  mkSelection,
  selectionContents,
} from '../../../src/kernel/diagram/subgraph/selection'

function host() {
  const builder = new DiagramBuilder()
  const outer = builder.ref(builder.root, 'Outer', relSig([IOTA]))
  const cut = builder.cut(builder.root)
  const inner = builder.ref(cut, 'Inner', relSig([IOTA, IOTA]))
  const shared = builder.wire( [
    { node: outer, port: { kind: 'arg', index: 0 } },
    { node: inner, port: { kind: 'arg', index: 0 } },
  ])
  const inside = builder.wire( [
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

describe('subgraph selection', () => {
  it('validates direct nodes, child regions, and explicit wires', () => {
    const value = host()
    expect(mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [value.outer],
      wires: [],
    })).toEqual({
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [value.outer],
      wires: [],
    })

    expect(() => mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [],
      nodes: [value.inner],
      wires: [],
    })).toThrowError(/not directly/)
    expect(() => mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut, value.cut],
      nodes: [],
      wires: [],
    })).toThrowError(/duplicate/)
  })

  it('classifies subtree-owned wires as internal and crossings as touching', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [],
      wires: [],
    })
    const contents = selectionContents(value.diagram, selection)

    expect([...contents.allRegions]).toEqual([value.cut])
    // The inside wire's pin lives in the cut, so it is selected content too.
    const insidePin = value.diagram.wires[value.inside]!.endpoints
      .find((endpoint) => endpoint.node !== value.inner)!.node
    expect([...contents.allNodes].sort()).toEqual([value.inner, insidePin].sort())
    expect(contents.internalWires).toEqual([value.inside])
    expect(contents.touchingWires).toEqual([value.shared])
  })

  it('allows an all-selected top-level wire to be chosen explicitly', () => {
    const value = host()
    const selection = mkSelection(value.diagram, {
      region: value.diagram.root,
      regions: [value.cut],
      nodes: [value.outer],
      wires: [value.shared],
    })

    expect(selectionContents(value.diagram, selection).internalWires)
      .toEqual([value.shared, value.inside].sort())
  })

  it('rejects unknown selection ids at every entry point', () => {
    const value = host()
    expect(() => selectionContents(value.diagram, {
      region: value.diagram.root,
      regions: [],
      nodes: ['ghost'],
      wires: [],
    })).toThrowError(/unknown node 'ghost'/)
  })
})
