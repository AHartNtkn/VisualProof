import { describe, expect, it } from 'vitest'
import {
  SpawnRecents,
  atomHeadOptions,
  buildSpawnCatalog,
  searchSpawnCatalog,
  snapshotSpawnInvocation,
} from '../../src/app/interact/spawn'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { BINARY, UNARY } from '../fixtures/zero-signature'

describe('structural spawn catalog', () => {
  it('groups and searches opaque definition IDs', () => {
    const catalog = buildSpawnCatalog([
      ['logic/Unary', { boundary: [0] }],
      ['Pair', { boundary: [0, 1] }],
    ])
    expect(catalog.groups.map((group) => group.label)).toEqual(['Unqualified', 'logic'])
    expect(searchSpawnCatalog(catalog, 'unary').map((entry) => entry.defId))
      .toEqual(['logic/Unary'])
    const recents = new SpawnRecents(1)
    recents.note('Pair')
    expect(recents.list(catalog).map((entry) => entry.defId)).toEqual(['Pair'])
  })

  it('offers visible relational head wires from inner to outer scope', () => {
    const builder = new DiagramBuilder()
    const outer = builder.relWire(builder.root, UNARY)
    const cut = builder.cut(builder.root)
    const inner = builder.relWire(cut, BINARY)
    const diagram = builder.build()
    expect(atomHeadOptions(diagram, cut)).toEqual([
      { wire: inner, arity: 2, position: 1, total: 2 },
      { wire: outer, arity: 1, position: 2, total: 2 },
    ])
    expect(() => atomHeadOptions(diagram, 'missing')).toThrow(/unknown region/)
  })

  it('snapshots invocation coordinates', () => {
    const input = { screen: { x: 1, y: 2 }, world: { x: 3, y: 4 }, region: 'r0' }
    const output = snapshotSpawnInvocation(input)
    expect(output).toEqual(input)
    expect(output).not.toBe(input)
  })
})
