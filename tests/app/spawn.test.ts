import { describe, expect, it } from 'vitest'
import {
  SpawnCascade,
  SpawnRecents,
  UNQUALIFIED_GROUP_LABEL,
  buildSpawnCatalog,
  searchSpawnCatalog,
  snapshotSpawnInvocation,
} from '../../src/app/interact/spawn'

const relations = (entries: readonly (readonly [string, number])[]) => new Map(
  entries.map(([defId, arity]) => [defId, { boundary: Array.from({ length: arity }, () => 'w') }] as const),
)

describe('real relation spawn catalog', () => {
  it('retains exact defIds and derives nested slash namespaces plus a stable unqualified group', () => {
    const catalog = buildSpawnCatalog(relations([
      ['plain', 0],
      ['order/lt', 2],
      ['arith/order/le', 2],
      ['arith/add', 3],
    ]))

    expect(catalog.entries.map((entry) => ({
      defId: entry.defId,
      namespace: entry.namespace,
      leaf: entry.leaf,
      arity: entry.arity,
    }))).toEqual([
      { defId: 'arith/add', namespace: 'arith', leaf: 'add', arity: 3 },
      { defId: 'arith/order/le', namespace: 'arith/order', leaf: 'le', arity: 2 },
      { defId: 'order/lt', namespace: 'order', leaf: 'lt', arity: 2 },
      { defId: 'plain', namespace: null, leaf: 'plain', arity: 0 },
    ])
    expect(catalog.groups.map((group) => ({
      namespace: group.namespace,
      label: group.label,
      ids: group.entries.map((entry) => entry.defId),
    }))).toEqual([
      { namespace: null, label: UNQUALIFIED_GROUP_LABEL, ids: ['plain'] },
      { namespace: 'arith', label: 'arith', ids: ['arith/add'] },
      { namespace: 'arith/order', label: 'arith/order', ids: ['arith/order/le'] },
      { namespace: 'order', label: 'order', ids: ['order/lt'] },
    ])
  })

  it('preserves every exact id accepted by the authoritative relation map', () => {
    const catalog = buildSpawnCatalog(relations([
      ['/leading', 1],
      ['trailing/', 2],
      ['double//slash', 3],
    ]))
    expect(catalog.entries.map(({ defId, namespace, leaf, arity }) => ({ defId, namespace, leaf, arity }))).toEqual([
      { defId: '/leading', namespace: '', leaf: 'leading', arity: 1 },
      { defId: 'double//slash', namespace: 'double/', leaf: 'slash', arity: 3 },
      { defId: 'trailing/', namespace: 'trailing', leaf: '', arity: 2 },
    ])
  })

  it('searches the complete id case-insensitively and ranks by match position, length, then id', () => {
    const catalog = buildSpawnCatalog(relations([
      ['arith/ADD', 3],
      ['add', 2],
      ['x/addition', 1],
      ['arith/madder', 4],
      ['unrelated', 0],
    ]))

    expect(searchSpawnCatalog(catalog, '  aDd  ').map((entry) => entry.defId)).toEqual([
      'add',
      'x/addition',
      'arith/ADD',
      'arith/madder',
    ])
    expect(searchSpawnCatalog(catalog, '')).toEqual([])
  })
})

describe('spawn recents', () => {
  it('is session-local, most-recent-first, deduped, capped, and filtered through the current catalog', () => {
    const catalog = buildSpawnCatalog(relations([
      ['a', 1],
      ['b', 2],
      ['c', 3],
    ]))
    const first = new SpawnRecents(2)
    const second = new SpawnRecents(2)

    first.note('a')
    first.note('b')
    first.note('a')
    first.note('c')

    expect(first.list(catalog).map((entry) => entry.defId)).toEqual(['c', 'a'])
    const withoutC = buildSpawnCatalog(relations([['a', 1], ['b', 2]]))
    expect(first.list(withoutC).map((entry) => entry.defId)).toEqual(['a'])
    expect(second.list(catalog)).toEqual([])

    first.note('a')
    expect(first.list(catalog).map((entry) => entry.defId)).toEqual(['a', 'c'])
  })

  it('refuses an invalid cap', () => {
    expect(() => new SpawnRecents(-1)).toThrow(/nonnegative integer/)
    expect(() => new SpawnRecents(1.5)).toThrow(/nonnegative integer/)
  })
})

describe('spawn invocation lifecycle value', () => {
  it('copies and freezes the exact screen/world/region snapshot', () => {
    const screen = { x: 11, y: 22 }
    const world = { x: -3, y: 7 }
    const snapshot = snapshotSpawnInvocation({ screen, world, region: 'r7' })

    screen.x = 100
    world.y = 200
    expect(snapshot).toEqual({ screen: { x: 11, y: 22 }, world: { x: -3, y: 7 }, region: 'r7' })
    expect(Object.isFrozen(snapshot)).toBe(true)
    expect(Object.isFrozen(snapshot.screen)).toBe(true)
    expect(Object.isFrozen(snapshot.world)).toBe(true)
  })

  it('has idempotent closed/disposed lifecycle methods without installing a DOM listener', () => {
    const host = { ownerDocument: {} } as HTMLElement
    const cascade = new SpawnCascade({ host, spawnTerm: () => {}, spawnRelation: () => {} })

    expect(cascade.isOpen).toBe(false)
    expect(cascade.close()).toBe(false)
    expect(cascade.escape()).toBe(false)
    expect(cascade.outside(null)).toBe(false)
    cascade.dispose()
    cascade.dispose()
    expect(() => cascade.open(
      { screen: { x: 0, y: 0 }, world: { x: 0, y: 0 }, region: 'r0' },
      relations([]),
    )).toThrow(/disposed/)
  })
})
