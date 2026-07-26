import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { mkDiagramWithBoundary } from '../../../src/kernel/diagram/boundary'
import { IOTA, relSig } from '../../../src/kernel/diagram/sig'
import { applyAtomSpawn, applyRefSpawn } from '../../../src/kernel/rules/spawn'

const ARITY_TWO = relSig([IOTA, IOTA])

function host() {
  const builder = new DiagramBuilder()
  const cut = builder.cut(builder.root)
  const sibling = builder.cut(builder.root)
  const relationWire = builder.relWire(cut, ARITY_TWO)
  const inner = builder.cut(cut)
  return {
    diagram: builder.build(),
    root: builder.root,
    cut,
    sibling,
    relationWire,
    inner,
  }
}

function definitions() {
  const body = new DiagramBuilder()
  const left = body.wire(body.root, [], IOTA)
  const right = body.wire(body.root, [], IOTA)
  return new Map([[
    'logic/R',
    mkDiagramWithBoundary(body.build(), [left, right]),
  ]])
}

function truthReificationDefinition(
  lookalike: 'none' | 'missing-witness' | 'asymmetric-material' = 'none',
) {
  const body = new DiagramBuilder()
  const forward = body.cut(body.root)
  const forwardConsequent = body.cut(forward)
  const reverse = body.cut(body.root)
  const reverseConsequent = body.cut(reverse)
  const forwardWitness = body.atom(forward, relSig([]))
  const reverseWitness = lookalike === 'missing-witness'
    ? undefined
    : body.atom(reverseConsequent, relSig([]))
  if (lookalike === 'asymmetric-material') {
    const extra = body.atom(forwardConsequent, relSig([]))
    body.wire(forwardConsequent, [{
      node: extra,
      port: { kind: 'head' },
    }], relSig([]))
  }
  const witness = body.wire(body.root, [
    { node: forwardWitness, port: { kind: 'head' } },
    ...(reverseWitness === undefined
      ? []
      : [{ node: reverseWitness, port: { kind: 'head' } } as const]),
  ], relSig([]))
  return mkDiagramWithBoundary(body.build(), [witness])
}

function capturedImplicationReification(
  lookalike: 'none' | 'permuted-captures' | 'unused-capture' = 'none',
) {
  const proposition = relSig([])
  const body = new DiagramBuilder()
  const forward = body.cut(body.root)
  const forwardConsequent = body.cut(forward)
  const reverse = body.cut(body.root)
  const reverseConsequent = body.cut(reverse)
  const forwardMaterial = body.cut(forwardConsequent)
  const forwardMaterialConsequent = body.cut(forwardMaterial)
  const reverseMaterial = body.cut(reverse)
  const reverseMaterialConsequent = body.cut(reverseMaterial)

  const forwardWitness = body.atom(forward, proposition)
  const reverseWitness = body.atom(reverseConsequent, proposition)
  const forwardLeft = body.atom(forwardMaterial, proposition)
  const forwardRight = body.atom(forwardMaterialConsequent, proposition)
  const reverseLeft = body.atom(reverseMaterial, proposition)
  const reverseRight = body.atom(reverseMaterialConsequent, proposition)

  const witness = body.wire(body.root, [
    { node: forwardWitness, port: { kind: 'head' } },
    { node: reverseWitness, port: { kind: 'head' } },
  ], proposition)
  const left = body.wire(body.root, [
    { node: forwardLeft, port: { kind: 'head' } },
    {
      node: lookalike === 'permuted-captures'
        ? reverseRight
        : reverseLeft,
      port: { kind: 'head' },
    },
  ], proposition)
  const right = body.wire(body.root, [
    { node: forwardRight, port: { kind: 'head' } },
    {
      node: lookalike === 'permuted-captures'
        ? reverseLeft
        : reverseRight,
      port: { kind: 'head' },
    },
  ], proposition)
  const boundary = [witness, left, right]
  if (lookalike === 'unused-capture') {
    boundary.push(body.wire(body.root, [], proposition))
  }
  return mkDiagramWithBoundary(body.build(), boundary)
}

describe('Phase-1 primitive spawning', () => {
  it('spawns a ref with signature-indexed argument wires', () => {
    const fixture = host()
    const result = applyRefSpawn(
      fixture.diagram,
      fixture.cut,
      'logic/R',
      ARITY_TWO,
      definitions(),
    )
    const ref = Object.values(result.nodes)[0]
    const freshWires = Object.entries(result.wires).filter(([id]) =>
      fixture.diagram.wires[id] === undefined)

    expect(ref).toMatchObject({
      kind: 'ref',
      region: fixture.cut,
      defId: 'logic/R',
      sig: ARITY_TWO,
    })
    expect(freshWires).toHaveLength(2)
    expect(freshWires.every(([, wire]) =>
      wire.scope === fixture.cut
      && wire.endpoints.length === 1)).toBe(true)
  })

  it('revalidates definition identity and signature', () => {
    const fixture = host()
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.cut,
      'logic/R',
      relSig([IOTA]),
      definitions(),
    )).toThrowError(/changed signature/)
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.cut,
      'missing',
      ARITY_TWO,
      definitions(),
    )).toThrowError(/no longer loaded/)
  })

  it('binds a new atom head to the named relational wire', () => {
    const fixture = host()
    const result = applyAtomSpawn(
      fixture.diagram,
      fixture.cut,
      fixture.relationWire,
    )

    expect(Object.values(result.nodes)).toEqual([
      expect.objectContaining({
        kind: 'atom',
        region: fixture.cut,
        sig: ARITY_TWO,
      }),
    ])
    expect(result.wires[fixture.relationWire]?.endpoints).toEqual([
      { node: 'n', port: { kind: 'head' } },
    ])
  })

  it('shares the flipped polarity gate and enforces wire scope', () => {
    const fixture = host()
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.root,
      'logic/R',
      ARITY_TWO,
      definitions(),
      'forward',
    )).toThrowError(/negative region/)
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.root,
      'logic/R',
      ARITY_TWO,
      definitions(),
      'backward',
    )).not.toThrow()

    expect(() => applyAtomSpawn(
      fixture.diagram,
      fixture.root,
      fixture.relationWire,
      'forward',
    )).toThrowError(/negative region/)
    expect(() => applyAtomSpawn(
      fixture.diagram,
      fixture.sibling,
      fixture.relationWire,
      'forward',
    )).toThrowError(/does not enclose/)
    expect(() => applyAtomSpawn(
      fixture.diagram,
      fixture.inner,
      fixture.relationWire,
      'backward',
    )).not.toThrow()
  })

  it('gives only exact checked reifications the full orientation/polarity matrix', () => {
    const fixture = host()
    const signature = relSig([relSig([])])
    const exact = new Map([[
      'logic/TruthReification',
      truthReificationDefinition(),
    ]])

    for (const region of [fixture.root, fixture.cut, fixture.inner]) {
      for (const orientation of ['forward', 'backward'] as const) {
        expect(() => applyRefSpawn(
          fixture.diagram,
          region,
          'logic/TruthReification',
          signature,
          exact,
          orientation,
        )).not.toThrow()
      }
    }

    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.root,
      'logic/R',
      ARITY_TWO,
      definitions(),
      'forward',
    )).toThrowError(/negative region/)
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.cut,
      'logic/R',
      ARITY_TWO,
      definitions(),
      'backward',
    )).toThrowError(/positive region/)
  })

  it.each([
    'missing-witness',
    'asymmetric-material',
  ] as const)(
    'rejects the same-signature %s lookalike at a positive scope',
    (lookalike) => {
      const fixture = host()
      const malformed = new Map([[
        'logic/TruthReification',
        truthReificationDefinition(lookalike),
      ]])

      expect(() => applyRefSpawn(
        fixture.diagram,
        fixture.root,
        'logic/TruthReification',
        relSig([relSig([])]),
        malformed,
        'forward',
      )).toThrowError(/exact reification definition/i)
    },
  )

  it('checks ordered capture pins and rejects unused capture boundaries', () => {
    const fixture = host()
    const exact = capturedImplicationReification()
    expect(() => applyRefSpawn(
      fixture.diagram,
      fixture.root,
      'logic/CapturedImplication',
      relSig(exact.boundary.map((wire) => exact.diagram.wires[wire]!.sig)),
      new Map([['logic/CapturedImplication', exact]]),
      'forward',
    )).not.toThrow()

    for (const lookalike of [
      'permuted-captures',
      'unused-capture',
    ] as const) {
      const malformed = capturedImplicationReification(lookalike)
      expect(() => applyRefSpawn(
        fixture.diagram,
        fixture.root,
        'logic/CapturedImplication',
        relSig(malformed.boundary.map((wire) =>
          malformed.diagram.wires[wire]!.sig)),
        new Map([['logic/CapturedImplication', malformed]]),
        'forward',
      )).toThrowError(/exact reification definition/i)
    }
  })
})
