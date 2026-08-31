import { describe, expect, it } from 'vitest'
import { publishOrderCatalogRevision } from '../../game/order-catalog-publication'
import {
  LiveOrderCatalog,
  decodeOrderCatalog,
  openingOrderCatalog,
} from '../../src/game/orders/catalog'
import { serializeOrderCatalog } from '../../src/game/orders/content-client'
import { initialOrderProgress, orderSession } from '../../src/game/orders/session'

function revisions() {
  const blank = serializeOrderCatalog(openingOrderCatalog.current)[0]!
  const before = decodeOrderCatalog([
    { ...blank, id: 'first', prerequisites: [] },
    { ...blank, id: 'second', prerequisites: [] },
  ])
  const after = decodeOrderCatalog([
    { ...blank, id: 'second', prerequisites: [] },
    { ...blank, id: 'third', prerequisites: [] },
  ])
  return { before, after }
}

describe('live order catalog publication', () => {
  it('writes content, updates the save lifecycle, and publishes one live revision', async () => {
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    const persisted: unknown[] = []
    const savedOrderIds: string[][] = []
    const renderedPots: unknown[][] = []

    await publishOrderCatalogRevision({
      candidate: after,
      contentClient: { save: async (content) => { persisted.push(content) } },
      reconcileSave: async (orderIds) => { savedOrderIds.push([...orderIds]) },
      catalog,
      orders,
      renderer: { setPots: (pots) => { renderedPots.push([...pots]) } },
      isCurrent: () => true,
    })

    expect(persisted).toEqual([serializeOrderCatalog(after)])
    expect(savedOrderIds).toEqual([['second', 'third']])
    expect(catalog.current).toBe(after)
    expect([...orders.progress.orders]).toEqual([
      ['second', { kind: 'pending' }],
      ['third', { kind: 'pending' }],
    ])
    expect(renderedPots).toEqual([[]])
  })

  it('does not rewrite player order lifecycles when catalog IDs are unchanged', async () => {
    const { before } = revisions()
    const candidate = decodeOrderCatalog(serializeOrderCatalog(before).map((definition) => ({
      ...definition,
      reward: definition.reward + 1,
    })))
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    let lifecycleWrites = 0

    await publishOrderCatalogRevision({
      candidate,
      contentClient: { save: async () => {} },
      reconcileSave: async () => { lifecycleWrites += 1 },
      catalog,
      orders,
      renderer: { setPots: () => {} },
      isCurrent: () => true,
    })

    expect(lifecycleWrites).toBe(0)
    expect(catalog.current).toBe(candidate)
  })

  it('leaves the running catalog unchanged when the content write fails', async () => {
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const progress = initialOrderProgress(before.definitions)
    const orders = orderSession(progress, catalog)

    await expect(publishOrderCatalogRevision({
      candidate: after,
      contentClient: { save: async () => { throw new Error('read-only content file') } },
      reconcileSave: async () => {},
      catalog,
      orders,
      renderer: { setPots: () => {} },
      isCurrent: () => true,
    })).rejects.toThrow('read-only content file')

    expect(catalog.current).toBe(before)
    expect(orders.progress).toBe(progress)
  })
})
