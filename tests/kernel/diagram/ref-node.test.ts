import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { portKey } from '../../../src/kernel/diagram/diagram'
import {
  spawnAtomNode,
  spawnRefNode,
} from '../../../src/kernel/diagram/spawn'
import { IOTA, relSig, sigKey } from '../../../src/kernel/diagram/sig'
import {
  applyAtomSpawn,
  applyRefSpawn,
} from '../../../src/kernel/rules/spawn'
import { bareWire, contentEndpoints } from '../../fixtures/pins'

describe('ref and atom spawning vocabulary', () => {
  it('spawnRefNode creates a ref with recursively signature-indexed argument wires', () => {
    const diagram = new DiagramBuilder().build()
    const sig = relSig([IOTA, relSig([])])
    const spawned = spawnRefNode(diagram, diagram.root, 'P', sig)
    const byPort = new Map(
      Object.values(spawned.diagram.wires).flatMap((wire) =>
        wire.endpoints.map((endpoint) => [portKey(endpoint.port), wire] as const)),
    )

    expect(spawned.diagram.nodes[spawned.node]).toEqual({
      kind: 'ref',
      region: diagram.root,
      defId: 'P',
      sig,
    })
    expect(sigKey(byPort.get('a:0')!.sig)).toBe('i')
    expect(sigKey(byPort.get('a:1')!.sig)).toBe('()')
  })

  it('spawnAtomNode binds a fresh atom head to an existing relational wire', () => {
    const builder = new DiagramBuilder()
    const sig = relSig([IOTA])
    const target = bareWire(builder, builder.root, sig)
    const spawned = spawnAtomNode(builder.build(), builder.root, target)

    expect(spawned.diagram.nodes[spawned.node]).toMatchObject({ kind: 'atom', sig })
    expect(contentEndpoints(spawned.diagram, target)).toEqual([
      { node: spawned.node, port: { kind: 'head' } },
    ])
  })

  it('applyRefSpawn uses the definition store and checks the full recursive signature', () => {
    const definitionBuilder = new DiagramBuilder()
    const nested = relSig([IOTA])
    const boundary = definitionBuilder.wire([], nested)
    const relation = definitionBuilder.buildOpen([boundary])
    const store = new Map([['P', relation]])

    const hostBuilder = new DiagramBuilder()
    const cut = hostBuilder.cut(hostBuilder.root)
    const host = hostBuilder.build()
    expect(() => applyRefSpawn(host, cut, 'P', relSig([nested]), store)).not.toThrow()
    expect(() => applyRefSpawn(host, cut, 'P', relSig([IOTA]), store))
      .toThrowError(/changed signature from '\(i\)' to '\(\(i\)\)'/)
  })

  it('applyAtomSpawn creates an atom through the atom-named rule entry', () => {
    const builder = new DiagramBuilder()
    const cut = builder.cut(builder.root)
    const target = bareWire(builder, builder.root, relSig([]))
    const spawned = applyAtomSpawn(builder.build(), cut, target)
    expect(Object.values(spawned.nodes).some((node) => node.kind === 'atom')).toBe(true)
  })
})
