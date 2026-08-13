import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { mkSelection } from '../../../src/kernel/diagram/subgraph/selection'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { applyDoubleCutElim, applyDoubleCutIntro } from '../../../src/kernel/rules/doublecut'
import { bareWire } from '../../fixtures/pins'

describe('double cut', () => {
  it('wraps a selection in two cuts and eliminates them as a fingerprint identity', () => {
    const builder = new DiagramBuilder()
    const selected = builder.ref(builder.root, 'P', relSig([IOTA]))
    const outside = builder.ref(builder.root, 'Q', relSig([IOTA]))
    builder.wire([
      { node: selected, port: { kind: 'arg', index: 0 } },
      { node: outside, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [selected],
      wires: [],
    })

    const wrapped = applyDoubleCutIntro(diagram, selection)
    const outer = Object.entries(wrapped.regions).find(
      ([id, region]) =>
        diagram.regions[id] === undefined
        && region.kind === 'cut'
        && region.parent === diagram.root,
    )![0]
    const inner = Object.entries(wrapped.regions).find(
      ([, region]) => region.kind === 'cut' && region.parent === outer,
    )![0]

    expect(wrapped.nodes[selected]!.region).toBe(inner)
    const spanning = Object.entries(wrapped.wires)
      .find(([, wire]) => wire.endpoints.length >= 2)![0]
    expect(derivedScope(wrapped, spanning)).toBe(diagram.root)
    expect(exploreForm(applyDoubleCutElim(wrapped, outer))).toBe(exploreForm(diagram))
  })

  it('wraps an empty selection as a bare double cut', () => {
    const builder = new DiagramBuilder()
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: diagram.root,
      regions: [],
      nodes: [],
      wires: [],
    })

    const wrapped = applyDoubleCutIntro(diagram, selection)

    expect(Object.keys(wrapped.regions)).toHaveLength(3)
  })

  it('rejects sheets, annulus nodes, annulus wires, and multiple child cuts', () => {
    const builder = new DiagramBuilder()
    const withNode = builder.cut(builder.root)
    builder.cut(withNode)
    builder.ref(withNode, 'annulus', relSig([]))
    const withChildren = builder.cut(builder.root)
    builder.cut(withChildren)
    builder.cut(withChildren)
    const withWire = builder.cut(builder.root)
    builder.cut(withWire)
    bareWire(builder, withWire)
    const clean = builder.cut(builder.root)
    builder.cut(clean)
    const diagram = builder.build()

    expect(() => applyDoubleCutElim(diagram, diagram.root))
      .toThrowError(/double-cut elimination requires a cut/)
    expect(() => applyDoubleCutElim(diagram, withNode))
      .toThrowError(/must contain exactly one child cut and nothing else/)
    expect(() => applyDoubleCutElim(diagram, withChildren))
      .toThrowError(/must contain exactly one child cut and nothing else/)
    expect(() => applyDoubleCutElim(diagram, withWire))
      .toThrowError(/must contain exactly one child cut and nothing else/)
    expect(() => applyDoubleCutElim(diagram, clean)).not.toThrow()
  })

  it('promotes inner-scoped wires and exact ref nodes to the outer parent', () => {
    const builder = new DiagramBuilder()
    const outer = builder.cut(builder.root)
    const inner = builder.cut(outer)
    const node = builder.ref(inner, 'P', relSig([IOTA]))
    const wire = builder.wire([
      { node, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    const eliminated = applyDoubleCutElim(diagram, outer)

    expect(derivedScope(eliminated, wire)).toBe(diagram.root)
    expect(eliminated.nodes[node]!.region).toBe(diagram.root)
    expect(eliminated.regions[outer]).toBeUndefined()
    expect(eliminated.regions[inner]).toBeUndefined()
  })

  it('parents introduction at the selected nested region rather than the sheet', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const node = builder.ref(enclosing, 'P', relSig([]))
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: enclosing,
      regions: [],
      nodes: [node],
      wires: [],
    })

    const wrapped = applyDoubleCutIntro(diagram, selection)
    const freshAtEnclosing = Object.entries(wrapped.regions).filter(
      ([id, region]) =>
        diagram.regions[id] === undefined
        && region.kind === 'cut'
        && region.parent === enclosing,
    )

    expect(freshAtEnclosing).toHaveLength(1)
  })

  it('promotes nested elimination content to the enclosing cut, not the sheet', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const outer = builder.cut(enclosing)
    const inner = builder.cut(outer)
    const node = builder.ref(inner, 'P', relSig([]))
    const diagram = builder.build()

    const eliminated = applyDoubleCutElim(diagram, outer)

    expect(eliminated.nodes[node]!.region).toBe(enclosing)
  })

  it('reparents identity nodes without introducing an alternate identity model', () => {
    const builder = new DiagramBuilder()
    const enclosing = builder.cut(builder.root)
    const identity = builder.identity(enclosing, IOTA, 2)
    const left = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    builder.pin(left, builder.root)
    const right = builder.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    builder.pin(right, builder.root)
    const diagram = builder.build()
    const selection = mkSelection(diagram, {
      region: enclosing,
      regions: [],
      nodes: [identity],
      wires: [],
    })

    const wrapped = applyDoubleCutIntro(diagram, selection)
    const moved = wrapped.nodes[identity]

    expect(moved).toMatchObject({ kind: 'identity', sig: IOTA, arity: 2 })
    expect(moved!.region).not.toBe(enclosing)
  })
})
