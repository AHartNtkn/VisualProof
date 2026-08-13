import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import { derivedScope } from '../../../src/kernel/diagram/regions'
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
    const left = builder.wire([
      { node: identity, port: { kind: 'identity', index: 0 } },
    ])
    builder.pin(left, builder.root)
    const right = builder.wire([
      { node: identity, port: { kind: 'identity', index: 1 } },
    ])
    builder.pin(right, builder.root)

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

  it('completes each free identity port with its own wire and pin, collapsing nothing', () => {
    const builder = new DiagramBuilder()
    const identity = builder.identity(builder.root, IOTA, 3)
    const diagram = builder.build()

    expect(diagram.nodes[identity]).toEqual({
      kind: 'identity',
      region: 'r0',
      sig: IOTA,
      arity: 3,
    })
    expect(Object.keys(diagram.wires)).toEqual(['w0', 'w1', 'w2'])
    for (const [index, wireId] of ['w0', 'w1', 'w2'].entries()) {
      const wire = diagram.wires[wireId]!
      expect(wire.endpoints).toContainEqual({
        node: identity,
        port: { kind: 'identity', index },
      })
      // The other end is a real node — the pin that holds the quantifier.
      const other = wire.endpoints.find((end) => end.node !== identity)!
      expect(diagram.nodes[other.node]).toEqual({
        kind: 'identity',
        region: 'r0',
        sig: IOTA,
        arity: 1,
      })
      expect(derivedScope(diagram, wireId)).toBe('r0')
    }
  })

  it('refuses to complete a wire with no ends at all', () => {
    const builder = new DiagramBuilder()
    builder.relWire(relSig([]))

    expect(() => builder.build()).toThrowError(/has no ends/)
  })
})
