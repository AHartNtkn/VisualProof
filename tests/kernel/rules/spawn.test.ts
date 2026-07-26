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
  const deep = builder.cut(inner)
  return {
    diagram: builder.build(),
    root: builder.root,
    cut,
    sibling,
    relationWire,
    inner,
    deep,
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

function reificationShapedDefinition(complete: boolean) {
  const body = new DiagramBuilder()
  const forward = body.cut(body.root)
  body.cut(forward)
  const reverse = body.cut(body.root)
  const reverseConsequent = body.cut(reverse)
  const forwardWitness = body.atom(forward, relSig([]))
  const reverseWitness = complete
    ? body.atom(reverseConsequent, relSig([]))
    : undefined
  const witness = body.wire(body.root, [
    { node: forwardWitness, port: { kind: 'head' } },
    ...(reverseWitness === undefined
      ? []
      : [{ node: reverseWitness, port: { kind: 'head' } } as const]),
  ], relSig([]))
  return mkDiagramWithBoundary(body.build(), [witness])
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

  it('uses the ordinary polarity matrix for every relation definition shape', () => {
    const fixture = host()
    const signature = relSig([relSig([])])
    const relationDefinitions = [
      new Map([['logic/R', definitions().get('logic/R')!]]),
      new Map([['logic/ReificationShape', reificationShapedDefinition(true)]]),
      new Map([['logic/ReificationLookalike', reificationShapedDefinition(false)]]),
    ] as const
    const regions = [
      { id: fixture.root, polarity: 'positive' },
      { id: fixture.cut, polarity: 'negative' },
      { id: fixture.inner, polarity: 'positive' },
      { id: fixture.deep, polarity: 'negative' },
    ] as const

    for (const relations of relationDefinitions) {
      const [defId, definition] = [...relations][0]!
      const expectedSig = defId === 'logic/R' ? ARITY_TWO : signature
      expect(definition.boundary).toHaveLength(expectedSig.args.length)
      for (const region of regions) {
        for (const orientation of ['forward', 'backward'] as const) {
          const allowed = orientation === 'forward'
            ? region.polarity === 'negative'
            : region.polarity === 'positive'
          const spawn = () => applyRefSpawn(
            fixture.diagram,
            region.id,
            defId,
            expectedSig,
            relations,
            orientation,
          )
          if (allowed) expect(spawn).not.toThrow()
          else expect(spawn).toThrowError(
            new RegExp(`${region.polarity === 'positive' ? 'negative' : 'positive'} region`),
          )
        }
      }
    }
  })
})
