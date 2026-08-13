import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import {
  spawnAtomNode,
  spawnRefNode,
} from '../../../src/kernel/diagram/spawn'
import { IOTA, relSig, sigKey } from '../../../src/kernel/diagram/sig'
import type { IdReservation } from '../../../src/kernel/diagram/subgraph/freshId'

describe('relation node spawning', () => {
  it('adds a ref with signature-indexed argument wires', () => {
    const diagram = new DiagramBuilder().build()
    const sig = relSig([IOTA, relSig([])])
    const spawned = spawnRefNode(diagram, diagram.root, 'P', sig)
    const byPort = new Map(
      Object.values(spawned.diagram.wires).flatMap((wire) =>
        wire.endpoints.map((endpoint) => [portKey(endpoint.port), wire] as const),
      ),
    )

    expect(spawned.diagram.nodes[spawned.node]).toEqual({
      kind: 'ref',
      region: diagram.root,
      defId: 'P',
      sig,
    })
    expect(sigKey(byPort.get('a:0')!.sig)).toBe(sigKey(IOTA))
    expect(sigKey(byPort.get('a:1')!.sig)).toBe(sigKey(relSig([])))
  })

  it('binds a fresh atom head to an existing relational wire', () => {
    const builder = new DiagramBuilder()
    const sig = relSig([IOTA])
    const target = builder.relWire( sig)
    const spawned = spawnAtomNode(
      builder.build(),
      builder.root,
      target,
    )

    expect(spawned.diagram.nodes[spawned.node]).toMatchObject({
      kind: 'atom',
      sig,
    })
    expect(spawned.diagram.wires[target]?.endpoints).toEqual([
      { node: spawned.node, port: { kind: 'head' } },
    ])
  })

  it('rejects missing and non-relational target wires', () => {
    const empty = new DiagramBuilder().build()
    expect(() => spawnAtomNode(empty, empty.root, 'ghost'))
      .toThrowError(/wire 'ghost' does not exist/)

    const builder = new DiagramBuilder()
    const iota = builder.wire( [])
    const diagram = builder.build()
    expect(() => spawnAtomNode(diagram, diagram.root, iota))
      .toThrowError(/has sig 'iota'/)
  })

  it('honors reserved node ids', () => {
    const builder = new DiagramBuilder()
    const target = builder.relWire( relSig([]))
    const reservation: IdReservation = {
      regions: new Set(),
      nodes: new Set(['n']),
      wires: new Set(),
    }
    const spawned = spawnAtomNode(
      builder.build(),
      builder.root,
      target,
      reservation,
    )
    expect(spawned.node).toBe('n_0')
  })
})
