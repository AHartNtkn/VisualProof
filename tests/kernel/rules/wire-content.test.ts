import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyCutAbsorb,
  applyCutWrap,
  applyEndsDelete,
  applyEndsSpawn,
  applyParallelFuse,
  applyParallelSplit,
} from '../../../src/kernel/rules/wire-content'
import { bareWire, contentEndpoints } from '../../fixtures/pins'

const UNARY = relSig([IOTA])

/** A unary relation wire with applied ends in the root and inside one cut. */
function appliedFixture() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const rootAtom = builder.atom(builder.root, UNARY)
  const cutAtom = builder.atom(cut, UNARY)
  const wire = builder.wire([
    { node: rootAtom, port: { kind: 'head' } },
    { node: cutAtom, port: { kind: 'head' } },
  ], UNARY)
  const rootArg = builder.wire([
    { node: rootAtom, port: { kind: 'arg', index: 0 } },
  ])
  const cutArg = builder.wire([
    { node: cutAtom, port: { kind: 'arg', index: 0 } },
  ])
  builder.pin(cutArg, builder.root)
  return { builder, cut, wire, rootAtom, cutAtom, rootArg, cutArg }
}

describe('cut wrap / cut absorb', () => {
  it('wraps every end in a fresh cut on a fresh wire and round-trips', () => {
    const { builder, wire, rootArg, cutArg } = appliedFixture()
    const diagram = builder.build()

    const wrapped = applyCutWrap(diagram, wire)

    expect(wrapped.wires[wire]).toBeUndefined()
    const freshWires = Object.keys(wrapped.wires)
      .filter((id) => diagram.wires[id] === undefined)
    expect(freshWires).toHaveLength(1)
    const fresh = freshWires[0]!
    expect(derivedScope(wrapped, fresh)).toBe(derivedScope(diagram, wire))
    expect(wrapped.wires[fresh]!.endpoints).toHaveLength(2)
    const freshRegions = Object.keys(wrapped.regions)
      .filter((id) => diagram.regions[id] === undefined)
    expect(freshRegions).toHaveLength(2)
    for (const endpoint of wrapped.wires[fresh]!.endpoints) {
      const node = wrapped.nodes[endpoint.node]!
      expect(node.kind).toBe('atom')
      expect(freshRegions).toContain(node.region)
    }
    expect(contentEndpoints(wrapped, rootArg)).toHaveLength(1)
    expect(contentEndpoints(wrapped, cutArg)).toHaveLength(1)

    const restored = applyCutAbsorb(wrapped, fresh)
    expect(exploreForm(restored)).toEqual(exploreForm(diagram))
  })

  it('refuses a wire with a non-applied endpoint', () => {
    const builder = new DiagramBuilder()
    const outer = builder.atom(builder.root, relSig([UNARY]))
    const applied = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: applied, port: { kind: 'head' } },
      { node: outer, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    builder.wire([
      { node: applied, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: outer, port: { kind: 'head' } },
    ], relSig([UNARY]))
    const diagram = builder.build()

    expect(() => applyCutWrap(diagram, wire))
      .toThrowError(/every endpoint .* to be an applied atom head/)
  })

  it('refuses absorbing when a cut holds more than its atom', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atom = builder.atom(cut, UNARY)
    const extra = builder.ref(cut, 'Noise', relSig([]))
    void extra
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyCutAbsorb(diagram, wire))
      .toThrowError(/exactly the applied atom/)
  })
})

describe('parallel split / parallel fuse', () => {
  it('splits every end into side-by-side ends on two fresh wires and round-trips', () => {
    const { builder, wire } = appliedFixture()
    const diagram = builder.build()

    const split = applyParallelSplit(diagram, wire)

    expect(split.wires[wire]).toBeUndefined()
    const freshWires = Object.keys(split.wires)
      .filter((id) => diagram.wires[id] === undefined)
    expect(freshWires).toHaveLength(2)
    for (const fresh of freshWires) {
      expect(derivedScope(split, fresh)).toBe(derivedScope(diagram, wire))
      expect(split.wires[fresh]!.endpoints).toHaveLength(2)
    }

    const fused = applyParallelFuse(split, freshWires[0]!, freshWires[1]!)
    expect(exploreForm(fused)).toEqual(exploreForm(diagram))
  })

  it('refuses fusing wires whose end multisets differ', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const a = builder.wire([
      { node: atomA, port: { kind: 'head' } },
    ], UNARY)
    const b = builder.wire([
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    const diagram = builder.build()

    expect(() => applyParallelFuse(diagram, a, b))
      .toThrowError(/pairwise co-located ends with identical arguments/)
  })

  it('refuses fusing wires of different signatures or scopes', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const unary = bareWire(builder, builder.root, UNARY)
    const binary = bareWire(builder, builder.root, relSig([IOTA, IOTA]))
    const nested = bareWire(builder, cut, UNARY)
    const diagram = builder.build()

    expect(() => applyParallelFuse(diagram, unary, binary))
      .toThrowError(/equal signatures/)
    expect(() => applyParallelFuse(diagram, unary, nested))
      .toThrowError(/equal scopes/)
  })
})

describe('ends delete / ends spawn', () => {
  it('deletes every end at a negative scope forward and round-trips via spawn', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const atom = builder.atom(scope, UNARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    // Both wires survive the delete as bare wires, so each carries the two
    // pins the floor requires once its attachment goes.
    builder.pin(wire, scope)
    builder.pin(wire, scope)
    const arg = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(arg, scope)
    builder.pin(arg, scope)
    const diagram = builder.build()

    const deleted = applyEndsDelete(diagram, wire)
    // The ends go; both wires survive as bare wires held by their pins.
    const surviving = Object.values(deleted.nodes)
    expect(surviving.map((node) =>
      node.kind === 'identity' && node.arity === 1 ? 'pin' : node.kind))
      .toEqual(surviving.map(() => 'pin'))
    expect(deleted.wires[wire]!.endpoints).toHaveLength(2)
    expect(deleted.wires[arg]!.endpoints).toHaveLength(2)

    const respawned = applyEndsSpawn(deleted, wire, [
      { region: scope, args: [arg] },
    ], 'backward')
    expect(exploreForm(respawned)).toEqual(exploreForm(diagram))
  })

  it('gates delete on the wire scope polarity in both orientations', () => {
    const builder = new DiagramBuilder()
    const atom = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const arg = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(arg, builder.root)
    builder.pin(arg, builder.root)
    const diagram = builder.build()

    expect(() => applyEndsDelete(diagram, wire))
      .toThrowError(/deleting a wire's ends requires a negative scope/)
    expect(() => applyEndsDelete(diagram, wire, 'backward')).not.toThrow()
  })

  it('gates spawn on the wire scope polarity and requires an endpoint-free wire', () => {
    const builder = new DiagramBuilder()
    const negative = builder.cut(builder.root)
    const rootWire = bareWire(builder, builder.root, relSig([]))
    const negativeWire = bareWire(builder, negative, relSig([]))
    const diagram = builder.build()

    expect(() => applyEndsSpawn(diagram, rootWire, [
      { region: builder.root, args: [] },
    ])).not.toThrow()
    expect(() => applyEndsSpawn(diagram, negativeWire, [
      { region: negative, args: [] },
    ])).toThrowError(/spawning a wire's ends requires a positive scope/)
    expect(() => applyEndsSpawn(diagram, negativeWire, [
      { region: negative, args: [] },
    ], 'backward')).not.toThrow()

    const spawned = applyEndsSpawn(diagram, rootWire, [
      { region: builder.root, args: [] },
    ])
    expect(() => applyEndsSpawn(spawned, rootWire, [
      { region: builder.root, args: [] },
    ])).toThrowError(/bare wire \(pin ends only\)/)
  })

  it('refuses spawn sites outside the wire scope or with mismatched arguments', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const wire = bareWire(builder, cut, UNARY)
    const outerArg = bareWire(builder, builder.root)
    const diagram = builder.build()

    expect(() => applyEndsSpawn(diagram, wire, [
      { region: builder.root, args: [outerArg] },
    ], 'backward')).toThrowError(/site region .* is not inside/)
    expect(() => applyEndsSpawn(diagram, wire, [
      { region: cut, args: [] },
    ], 'backward')).toThrowError(/expects 1 argument/)
  })
})
