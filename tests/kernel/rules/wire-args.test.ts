import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { exploreForm } from '../../../src/kernel/diagram/canonical/explore'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import {
  applyAbstractFormal,
  applyApplyFormal,
  applyArgContract,
  applyArgDrop,
  applyArgDuplicate,
  applyArgExtend,
  applyArgPermute,
  applyArityShift,
  applyArityUnshift,
  applyIdentityAbstract,
  applyIdentityLeaf,
} from '../../../src/kernel/rules/wire-args'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])

/** A binary relation wire with one applied end inside a cut. */
function binaryFixture() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const atom = builder.atom(cut, BINARY)
  const wire = builder.wire(builder.root, [
    { node: atom, port: { kind: 'head' } },
  ], BINARY)
  const first = builder.wire(builder.root, [
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  const second = builder.wire(builder.root, [
    { node: atom, port: { kind: 'arg', index: 1 } },
  ])
  return { builder, cut, atom, wire, first, second }
}

describe('arity shift / unshift', () => {
  it('adds a per-end locally scoped argument and round-trips', () => {
    const { builder, cut, wire } = binaryFixture()
    const diagram = builder.build()

    const shifted = applyArityShift(diagram, wire, IOTA)

    expect(shifted.wires[wire]).toBeUndefined()
    const fresh = Object.keys(shifted.wires).find((id) =>
      diagram.wires[id] === undefined && shifted.wires[id]!.sig.kind === 'rel')!
    expect(shifted.wires[fresh]!.sig).toEqual(relSig([IOTA, IOTA, IOTA]))
    const locals = Object.keys(shifted.wires).filter((id) =>
      diagram.wires[id] === undefined && id !== fresh)
    expect(locals).toHaveLength(1)
    expect(shifted.wires[locals[0]!]!.scope).toBe(cut)
    expect(shifted.wires[locals[0]!]!.endpoints).toHaveLength(1)

    const restored = applyArityUnshift(shifted, fresh, 2)
    expect(exploreForm(restored)).toEqual(exploreForm(diagram))
  })

  it('refuses unshift when the position wire is shared or outer-scoped', () => {
    const { builder, wire, second } = binaryFixture()
    const extraAtom = builder.atom(builder.root, UNARY)
    builder.wire(builder.root, [
      { node: extraAtom, port: { kind: 'head' } },
    ], UNARY)
    const secondUse = { node: extraAtom, port: { kind: 'arg', index: 0 } } as const
    void secondUse
    const diagram = builder.build()
    void second

    expect(() => applyArityUnshift(diagram, wire, 1))
      .toThrowError(/locally scoped .* only endpoint|scoped at the end's region/)
  })
})

describe('argument permute / duplicate / contract', () => {
  it('permutes argument positions and inverts', () => {
    const { builder, wire, first, second } = binaryFixture()
    const diagram = builder.build()

    const permuted = applyArgPermute(diagram, wire, [1, 0])
    const fresh = Object.keys(permuted.wires).find((id) =>
      diagram.wires[id] === undefined)!
    expect(permuted.wires[fresh]!.sig).toEqual(BINARY)
    const end = permuted.wires[fresh]!.endpoints[0]!
    const argWires = [0, 1].map((index) =>
      Object.keys(permuted.wires).find((id) =>
        permuted.wires[id]!.endpoints.some((endpoint) =>
          endpoint.node === end.node
          && endpoint.port.kind === 'arg'
          && endpoint.port.index === index)))
    expect(argWires).toEqual([second, first])

    const inverted = applyArgPermute(permuted, fresh, [1, 0])
    expect(exploreForm(inverted)).toEqual(exploreForm(diagram))
  })

  it('duplicates a position onto the same wire and contracts back', () => {
    const { builder, wire } = binaryFixture()
    const diagram = builder.build()

    const duplicated = applyArgDuplicate(diagram, wire, 0)
    const fresh = Object.keys(duplicated.wires).find((id) =>
      diagram.wires[id] === undefined)!
    expect(duplicated.wires[fresh]!.sig).toEqual(relSig([IOTA, IOTA, IOTA]))

    const contracted = applyArgContract(duplicated, fresh, 0)
    expect(exploreForm(contracted)).toEqual(exploreForm(diagram))
  })

  it('refuses contracting positions on different wires', () => {
    const { builder, wire } = binaryFixture()
    const diagram = builder.build()

    expect(() => applyArgContract(diagram, wire, 0))
      .toThrowError(/attach to the same wire/)
  })

  it('refuses an invalid permutation', () => {
    const { builder, wire } = binaryFixture()
    const diagram = builder.build()

    expect(() => applyArgPermute(diagram, wire, [0, 0]))
      .toThrowError(/permutation/)
  })
})

describe('argument drop / extend', () => {
  it('drops a position at a negative scope and extends back', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const atom = builder.atom(scope, BINARY)
    const wire = builder.wire(scope, [
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const dropped_ = builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    const dropped = applyArgDrop(diagram, wire, 1)
    const fresh = Object.keys(dropped.wires).find((id) =>
      diagram.wires[id] === undefined)!
    expect(dropped.wires[fresh]!.sig).toEqual(UNARY)
    expect(dropped.wires[dropped_]!.endpoints).toEqual([])

    const end = dropped.wires[fresh]!.endpoints[0]!
    const extended = applyArgExtend(
      dropped,
      fresh,
      1,
      IOTA,
      new Map([[end.node, dropped_]]),
      'backward',
    )
    expect(exploreForm(extended)).toEqual(exploreForm(diagram))
  })

  it('gates drop on the wire scope polarity for per-end-varying attachments', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire(builder.root, [
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    builder.wire(builder.root, [{ node: atomA, port: { kind: 'arg', index: 0 } }])
    builder.wire(builder.root, [{ node: atomB, port: { kind: 'arg', index: 0 } }])
    const diagram = builder.build()

    expect(() => applyArgDrop(diagram, wire, 0))
      .toThrowError(/dropping an argument requires a negative scope/)
    expect(() => applyArgDrop(diagram, wire, 0, 'backward')).not.toThrow()
  })

  it('drops and extends ungated when the attachment is uniform and scope-visible', () => {
    const builder = new DiagramBuilder()
    const shared = builder.wire(builder.root, [])
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire(builder.root, [
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    builder.wire(builder.root, [
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    void shared
    const diagram = builder.build()

    expect(() => applyArgDrop(diagram, wire, 0)).not.toThrow()
  })

  it('refuses an extend map that does not cover every end', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const wire = builder.relWire(scope, relSig([]))
    const spawnArg = builder.wire(scope, [])
    void spawnArg
    const diagram = builder.build()

    expect(() => applyArgExtend(diagram, wire, 0, IOTA, new Map(), 'backward'))
      .not.toThrow()

    const full = new DiagramBuilder()
    const negative = full.cut(full.root)
    const atom = full.atom(negative, BINARY)
    const fullWire = full.wire(negative, [
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    full.wire(negative, [{ node: atom, port: { kind: 'arg', index: 0 } }])
    full.wire(negative, [{ node: atom, port: { kind: 'arg', index: 1 } }])
    const fullDiagram = full.build()
    expect(() => applyArgExtend(
      fullDiagram,
      fullWire,
      0,
      IOTA,
      new Map(),
      'backward',
    )).toThrowError(/covering every end/)
  })
})

describe('apply-formal / abstract-formal', () => {
  it('applies the formal at a negative scope and abstracts back', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const higher = relSig([UNARY, IOTA])
    const atom = builder.atom(scope, higher)
    const wire = builder.wire(scope, [
      { node: atom, port: { kind: 'head' } },
    ], higher)
    const target = builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    const applied = applyApplyFormal(diagram, wire, 0)
    expect(applied.wires[wire]).toBeUndefined()
    const newEnd = applied.wires[target]!.endpoints.find((endpoint) =>
      endpoint.port.kind === 'head')!
    expect(applied.nodes[newEnd.node]!.kind).toBe('atom')

    const restored = applyAbstractFormal(
      applied,
      [newEnd.node],
      scope,
      'backward',
    )
    expect(exploreForm(restored)).toEqual(exploreForm(diagram))
  })

  it('refuses apply-formal when the position sig does not match the rest', () => {
    const { builder, wire } = binaryFixture()
    const diagram = builder.build()

    expect(() => applyApplyFormal(diagram, wire, 0, 'backward'))
      .toThrowError(/must equal the relation signature of the remaining/)
  })
})

describe('identity leaf / abstract', () => {
  it('turns ends into identity nodes at a negative scope and abstracts back', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const atom = builder.atom(scope, BINARY)
    const wire = builder.wire(scope, [
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire(builder.root, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    const leafed = applyIdentityLeaf(diagram, wire)
    expect(leafed.wires[wire]).toBeUndefined()
    const identities = Object.entries(leafed.nodes)
      .filter(([, node]) => node.kind === 'identity')
    expect(identities).toHaveLength(1)

    const restored = applyIdentityAbstract(
      leafed,
      [identities[0]![0]],
      scope,
      'backward',
    )
    expect(exploreForm(restored)).toEqual(exploreForm(diagram))
  })

  it('gates every directional argument rule on the governing scope polarity', () => {
    const builder = new DiagramBuilder()
    const higher = relSig([UNARY, IOTA])
    const higherAtom = builder.atom(builder.root, higher)
    const higherWire = builder.wire(builder.root, [
      { node: higherAtom, port: { kind: 'head' } },
    ], higher)
    builder.wire(builder.root, [
      { node: higherAtom, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    builder.wire(builder.root, [
      { node: higherAtom, port: { kind: 'arg', index: 1 } },
    ])
    const pairAtom = builder.atom(builder.root, BINARY)
    const pairWire = builder.wire(builder.root, [
      { node: pairAtom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire(builder.root, [
      { node: pairAtom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: pairAtom, port: { kind: 'arg', index: 1 } },
    ])
    const diagram = builder.build()

    expect(() => applyApplyFormal(diagram, higherWire, 0))
      .toThrowError(/requires a negative scope/)
    expect(() => applyIdentityLeaf(diagram, pairWire))
      .toThrowError(/requires a negative scope/)
    expect(() => applyAbstractFormal(diagram, [pairAtom], builder.root, 'backward'))
      .toThrowError(/requires a negative scope/)
    const withIdentity = new DiagramBuilder()
    const cut = withIdentity.cut(withIdentity.root)
    const eq = withIdentity.identity(cut, IOTA, 2)
    withIdentity.wire(withIdentity.root, [
      { node: eq, port: { kind: 'identity', index: 0 } },
    ])
    withIdentity.wire(withIdentity.root, [
      { node: eq, port: { kind: 'identity', index: 1 } },
    ])
    const identityDiagram = withIdentity.build()
    expect(() => applyIdentityAbstract(
      identityDiagram,
      [eq],
      withIdentity.root,
      'backward',
    )).toThrowError(/requires a negative scope/)
  })

  it('refuses identity leaf on mixed argument signatures', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const mixed = relSig([IOTA, UNARY])
    const atom = builder.atom(scope, mixed)
    const wire = builder.wire(scope, [
      { node: atom, port: { kind: 'head' } },
    ], mixed)
    builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire(scope, [
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], UNARY)
    const diagram = builder.build()

    expect(() => applyIdentityLeaf(diagram, wire))
      .toThrowError(/equal argument signatures/)
  })
})
