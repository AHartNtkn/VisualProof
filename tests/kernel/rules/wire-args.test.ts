import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { derivedScope } from '../../../src/kernel/diagram/regions'
import { contentEndpoints } from '../../fixtures/pins'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyVacuityInsert } from '../../../src/kernel/rules/identity-rules'
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
  applyRefAbstract,
  applyRefLeaf,
} from '../../../src/kernel/rules/wire-args'
import { ScopePreservationError } from '../../../src/kernel/rules/wire-ends'

const UNARY = relSig([IOTA])
const BINARY = relSig([IOTA, IOTA])

/** A binary relation wire with one applied end inside a cut. */
function binaryFixture() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const atom = builder.atom(cut, BINARY)
  const wire = builder.wire([
    { node: atom, port: { kind: 'head' } },
  ], BINARY)
  builder.pin(wire, builder.root)
  const first = builder.wire([
    { node: atom, port: { kind: 'arg', index: 0 } },
  ])
  builder.pin(first, builder.root)
  const second = builder.wire([
    { node: atom, port: { kind: 'arg', index: 1 } },
  ])
  builder.pin(second, builder.root)
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
    expect(derivedScope(shifted, locals[0]!)).toBe(cut)
    expect(contentEndpoints(shifted, locals[0]!)).toHaveLength(1)

    const restored = applyArityUnshift(shifted, fresh, 2)
    expect(sameDiagram(restored, diagram)).toBe(true)
  })

  it('refuses unshift when the position wire is shared or outer-scoped', () => {
    const { builder, wire, second } = binaryFixture()
    const extraAtom = builder.atom(builder.root, UNARY)
    builder.wire([
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
    expect(sameDiagram(inverted, diagram)).toBe(true)
  })

  it('duplicates a position onto the same wire and contracts back', () => {
    const { builder, wire } = binaryFixture()
    const diagram = builder.build()

    const duplicated = applyArgDuplicate(diagram, wire, 0)
    const fresh = Object.keys(duplicated.wires).find((id) =>
      diagram.wires[id] === undefined)!
    expect(duplicated.wires[fresh]!.sig).toEqual(relSig([IOTA, IOTA, IOTA]))

    const contracted = applyArgContract(duplicated, fresh, 0)
    expect(sameDiagram(contracted, diagram)).toBe(true)
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
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    const dropped_ = builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    // Two pins: the position wire survives the drop as a bare wire, and the
    // two-end floor forbids leaving it under one end.
    builder.pin(dropped_, scope)
    builder.pin(dropped_, scope)
    const diagram = builder.build()

    const dropped = applyArgDrop(diagram, wire, 1)
    const fresh = Object.keys(dropped.wires).find((id) =>
      diagram.wires[id] === undefined)!
    expect(dropped.wires[fresh]!.sig).toEqual(UNARY)
    expect(dropped.wires[dropped_]!.endpoints.map((endpoint) =>
      dropped.nodes[endpoint.node]!.kind)).toEqual(['identity', 'identity'])

    const end = dropped.wires[fresh]!.endpoints[0]!
    const extended = applyArgExtend(
      dropped,
      fresh,
      1,
      IOTA,
      new Map([[end.node, dropped_]]),
      'backward',
    )
    expect(sameDiagram(extended, diagram)).toBe(true)
  })

  it('gates drop on the wire scope polarity for per-end-varying attachments', () => {
    const builder = new DiagramBuilder()
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    // The dropped-position wires survive the drop as bare wires, so each
    // needs the two pins the floor requires once its atom end goes.
    const argA = builder.wire([{ node: atomA, port: { kind: 'arg', index: 0 } }])
    builder.pin(argA, builder.root)
    builder.pin(argA, builder.root)
    const argB = builder.wire([{ node: atomB, port: { kind: 'arg', index: 0 } }])
    builder.pin(argB, builder.root)
    builder.pin(argB, builder.root)
    const diagram = builder.build()

    expect(() => applyArgDrop(diagram, wire, 0))
      .toThrowError(/dropping an argument requires a negative scope/)
    expect(() => applyArgDrop(diagram, wire, 0, 'backward')).not.toThrow()
  })

  it('drops and extends ungated when the attachment is uniform and scope-visible', () => {
    const builder = new DiagramBuilder()
    const shared = builder.wire([])
    builder.pin(shared, builder.root)
    builder.pin(shared, builder.root)
    const atomA = builder.atom(builder.root, UNARY)
    const atomB = builder.atom(builder.root, UNARY)
    const wire = builder.wire([
      { node: atomA, port: { kind: 'head' } },
      { node: atomB, port: { kind: 'head' } },
    ], UNARY)
    const argument = builder.wire([
      { node: atomA, port: { kind: 'arg', index: 0 } },
      { node: atomB, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(argument, builder.root)
    builder.pin(argument, builder.root)
    void shared
    const diagram = builder.build()

    expect(() => applyArgDrop(diagram, wire, 0)).not.toThrow()
  })

  it('refuses an extend map that does not cover every end', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const wire = builder.relWire(relSig([]))
    builder.pin(wire, scope)
    builder.pin(wire, scope)
    const spawnArg = builder.wire([])
    builder.pin(spawnArg, scope)
    builder.pin(spawnArg, scope)
    void spawnArg
    const diagram = builder.build()

    expect(() => applyArgExtend(diagram, wire, 0, IOTA, new Map(), 'backward'))
      .not.toThrow()

    const full = new DiagramBuilder()
    const negative = full.cut(full.root)
    const atom = full.atom(negative, BINARY)
    const fullWire = full.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    full.wire([{ node: atom, port: { kind: 'arg', index: 0 } }])
    full.wire([{ node: atom, port: { kind: 'arg', index: 1 } }])
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

describe('argument drop keeps the dropped attachment quantifier in place', () => {
  /** R(p,q) on the sheet, ¬(R(p,p) ∧ pin p): p reads at the sheet only through the first end. */
  function dropFixture() {
    const BINARY = relSig([IOTA, IOTA])
    const b = new DiagramBuilder()
    const cut = b.cut(b.root)
    const a = b.atom(b.root, BINARY)
    const c = b.atom(cut, BINARY)
    const R = b.wire([{ node: a, port: { kind: 'head' } }, { node: c, port: { kind: 'head' } }], BINARY)
    const p = b.wire([
      { node: a, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 0 } },
      { node: c, port: { kind: 'arg', index: 1 } },
    ])
    b.pin(p, cut)
    const q = b.wire([{ node: a, port: { kind: 'arg', index: 1 } }])
    b.pin(q, b.root)
    return { d: b.build(), R, p, cut }
  }

  it('refuses the ungated uniform drop that would sink the attachment under a cut', () => {
    const { d, R, p } = dropFixture()
    expect(derivedScope(d, p)).toBe(d.root)
    // BUG: p is "kept elsewhere" (position 1 of the cut end) and was exempt
    // from the scope check, so the drop went through and ∃p moved into the cut.
    expect(() => applyArgDrop(d, R, 0)).toThrow(ScopePreservationError)
  })

  it('accepts the drop once the attachment is pinned at its scope', () => {
    const { d, R, p } = dropFixture()
    const held = applyVacuityInsert(d, {
      kind: 'pin', wire: p, node: 'hold_p', region: d.root,
    })
    const out = applyArgDrop(held, R, 0)
    expect(derivedScope(out, p)).toBe(d.root)
  })
})

describe('apply-formal / abstract-formal', () => {
  it('applies the formal at a negative scope and abstracts back', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const higher = relSig([UNARY, IOTA])
    const atom = builder.atom(scope, higher)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], higher)
    const target = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    builder.wire([
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
    expect(sameDiagram(restored, diagram)).toBe(true)
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
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], BINARY)
    const firstArg = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(firstArg, builder.root)
    const secondArg = builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ])
    builder.pin(secondArg, builder.root)
    const diagram = builder.build()

    const leafed = applyIdentityLeaf(diagram, wire)
    expect(leafed.wires[wire]).toBeUndefined()
    const identities = Object.entries(leafed.nodes)
      .filter(([id, node]) => node.kind === 'identity' && diagram.nodes[id] === undefined)
    expect(identities).toHaveLength(1)

    const restored = applyIdentityAbstract(
      leafed,
      [identities[0]![0]],
      scope,
      'backward',
    )
    expect(sameDiagram(restored, diagram)).toBe(true)
  })

  it('gates every directional argument rule on the governing scope polarity', () => {
    const builder = new DiagramBuilder()
    const higher = relSig([UNARY, IOTA])
    const higherAtom = builder.atom(builder.root, higher)
    const higherWire = builder.wire([
      { node: higherAtom, port: { kind: 'head' } },
    ], higher)
    builder.wire([
      { node: higherAtom, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    builder.wire([
      { node: higherAtom, port: { kind: 'arg', index: 1 } },
    ])
    const pairAtom = builder.atom(builder.root, BINARY)
    const pairWire = builder.wire([
      { node: pairAtom, port: { kind: 'head' } },
    ], BINARY)
    builder.wire([
      { node: pairAtom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
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
    const eqLeft = withIdentity.wire([
      { node: eq, port: { kind: 'identity', index: 0 } },
    ])
    withIdentity.pin(eqLeft, withIdentity.root)
    const eqRight = withIdentity.wire([
      { node: eq, port: { kind: 'identity', index: 1 } },
    ])
    withIdentity.pin(eqRight, withIdentity.root)
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
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], mixed)
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.wire([
      { node: atom, port: { kind: 'arg', index: 1 } },
    ], UNARY)
    const diagram = builder.build()

    expect(() => applyIdentityLeaf(diagram, wire))
      .toThrowError(/equal argument signatures/)
  })
})

describe('ref leaf / abstract', () => {
  const unaryDefinition = () => {
    const definitionBuilder = new DiagramBuilder()
    const formal = definitionBuilder.wire([])
    return definitionBuilder.buildOpen([formal])
  }
  const definitions = () => new Map([['D', unaryDefinition()]])

  /** A unary wire applied at one atom inside a cut, argument at the root. */
  const applied = () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const atom = builder.atom(scope, UNARY)
    const wire = builder.wire([
      { node: atom, port: { kind: 'head' } },
    ], UNARY)
    const argument = builder.wire([
      { node: atom, port: { kind: 'arg', index: 0 } },
    ])
    builder.pin(argument, builder.root)
    return { builder, scope, atom, wire, argument }
  }

  it('turns ends into references at a negative scope and abstracts back', () => {
    const { builder, scope, wire, argument } = applied()
    const diagram = builder.build()

    const leafed = applyRefLeaf(diagram, wire, 'D', definitions())

    expect(leafed.wires[wire]).toBeUndefined()
    const references = Object.entries(leafed.nodes)
      .filter(([, node]) => node.kind === 'ref')
    expect(references).toHaveLength(1)
    const [referenceId, reference] = references[0]!
    if (reference.kind !== 'ref') throw new Error('unreachable')
    expect(reference.defId).toBe('D')
    expect(reference.sig).toEqual(UNARY)
    expect(leafed.wires[argument]!.endpoints.filter((endpoint) =>
      leafed.nodes[endpoint.node]!.kind === 'ref')).toEqual([
      { node: referenceId, port: { kind: 'arg', index: 0 } },
    ])

    const restored = applyRefAbstract(leafed, [referenceId], scope, 'backward')
    expect(sameDiagram(restored, diagram)).toBe(true)
  })

  it('gates both directions on the governing scope polarity', () => {
    const positiveBuilder = new DiagramBuilder()
    const positiveAtom = positiveBuilder.atom(positiveBuilder.root, UNARY)
    const positiveWire = positiveBuilder.wire([
      { node: positiveAtom, port: { kind: 'head' } },
    ], UNARY)
    positiveBuilder.wire([
      { node: positiveAtom, port: { kind: 'arg', index: 0 } },
    ])
    const positive = positiveBuilder.build()

    expect(() => applyRefLeaf(positive, positiveWire, 'D', definitions()))
      .toThrowError(/ref leaf requires a negative/)
    expect(() => applyRefLeaf(positive, positiveWire, 'D', definitions(), 'backward'))
      .not.toThrow()

    const { builder, scope, wire } = applied()
    const negative = builder.build()
    const leafed = applyRefLeaf(negative, wire, 'D', definitions())
    const reference = Object.entries(leafed.nodes)
      .find(([, node]) => node.kind === 'ref')![0]

    expect(() => applyRefAbstract(leafed, [reference], scope))
      .toThrowError(/ref abstract requires a positive/)
    expect(() => applyRefAbstract(leafed, [reference], scope, 'backward'))
      .not.toThrow()
  })

  it('refuses unknown definitions, mismatched signatures, and unapplied ends', () => {
    const { builder, wire } = applied()
    const diagram = builder.build()

    expect(() => applyRefLeaf(diagram, wire, 'missing', definitions()))
      .toThrowError(/no relation named 'missing'/)

    const binaryBuilder = new DiagramBuilder()
    const binaryFormals = [
      binaryBuilder.wire([]),
      binaryBuilder.wire([]),
    ]
    const binaryDefinition = binaryBuilder.buildOpen(binaryFormals)
    expect(() => applyRefLeaf(diagram, wire, 'D', new Map([['D', binaryDefinition]])))
      .toThrowError(/does not match/)

    const mixedBuilder = new DiagramBuilder()
    const mixedScope = mixedBuilder.cut(mixedBuilder.root)
    const mixedAtom = mixedBuilder.atom(mixedScope, UNARY)
    const consumer = mixedBuilder.atom(mixedScope, relSig([UNARY]))
    mixedBuilder.wire([
      { node: consumer, port: { kind: 'head' } },
    ], relSig([UNARY]))
    const mixedWire = mixedBuilder.wire([
      { node: mixedAtom, port: { kind: 'head' } },
      { node: consumer, port: { kind: 'arg', index: 0 } },
    ], UNARY)
    const mixed = mixedBuilder.build()
    expect(() => applyRefLeaf(mixed, mixedWire, 'D', definitions()))
      .toThrowError(/applied atom head/)
  })

  it('refuses abstracting references to different definitions', () => {
    const builder = new DiagramBuilder()
    const scope = builder.cut(builder.root)
    const first = builder.ref(scope, 'D', UNARY)
    const second = builder.ref(scope, 'E', UNARY)
    for (const node of [first, second]) {
      const argument = builder.wire([
        { node, port: { kind: 'arg', index: 0 } },
      ])
      builder.pin(argument, builder.root)
    }
    const diagram = builder.build()

    expect(() => applyRefAbstract(diagram, [first, second], builder.root))
      .toThrowError(/one shared definition/)
  })
})
