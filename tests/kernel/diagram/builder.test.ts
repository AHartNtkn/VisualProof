import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import { IOTA, relSig, sigKey } from '../../../src/kernel/diagram/sig'

describe('DiagramBuilder', () => {
  it('creates deterministic cuts, atoms, refs, and typed automatic wires', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const atomSig = relSig([IOTA])
    const atom = builder.atom(cut, atomSig)
    const ref = builder.ref(cut, 'P', relSig([IOTA, relSig([])]))
    const diagram = builder.build()

    expect(cut).toBe('r1')
    expect(atom).toBe('n0')
    expect(ref).toBe('n1')
    const byPort = new Map(
      Object.values(diagram.wires).flatMap((wire) =>
        wire.endpoints.map((endpoint) => [
          `${endpoint.node}:${portKey(endpoint.port)}`,
          wire,
        ] as const),
      ),
    )
    expect(sigKey(byPort.get('n0:hd')!.sig)).toBe(sigKey(atomSig))
    expect(sigKey(byPort.get('n0:a:0')!.sig)).toBe(sigKey(IOTA))
    expect(sigKey(byPort.get('n1:a:0')!.sig)).toBe(sigKey(IOTA))
    expect(sigKey(byPort.get('n1:a:1')!.sig)).toBe(sigKey(relSig([])))
  })

  it('keeps an explicitly outer-scoped identity and build is repeatable', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const identity = builder.identity(cut, IOTA, 2)
    builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    builder.wire(builder.root, [
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])

    const first = builder.build()
    const second = builder.build()
    expect(first).toEqual(second)
    expect(first.nodes[identity]).toEqual({
      kind: 'identity',
      region: cut,
      sig: IOTA,
      arity: 2,
    })
  })

  it('auto-created same-scope identity wires normalize away eagerly', () => {
    const builder = new DiagramBuilder()
    builder.identity(builder.root, IOTA, 3)
    const diagram = builder.build()

    expect(diagram.nodes).toEqual({})
    expect(Object.keys(diagram.wires)).toEqual(['w0'])
  })
})
