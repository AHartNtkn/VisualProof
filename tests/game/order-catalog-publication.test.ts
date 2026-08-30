import { describe, expect, it } from 'vitest'
import { publishOrderCatalogRevision } from '../../game/order-catalog-publication'
import { commitWorldShutdown } from '../../game/world-lifecycle'
import {
  LiveOrderCatalog,
  decodeOrderCatalog,
} from '../../src/game/orders/catalog'
import { serializeOrderCatalog } from '../../src/game/orders/content-client'
import { initialOrderProgress, orderSession } from '../../src/game/orders/session'
import { SaveWriter } from '../../src/game/save-writer'
import { openingOrderCatalog } from '../../src/game/orders/catalog'

function deferred<T>(): {
  readonly promise: Promise<T>
  resolve(value: T): void
  reject(error: unknown): void
} {
  let resolve!: (value: T) => void
  let reject!: (error: unknown) => void
  const promise = new Promise<T>((done, fail) => {
    resolve = done
    reject = fail
  })
  return { promise, resolve, reject }
}

function revisions() {
  const blank = serializeOrderCatalog(openingOrderCatalog.current)[0]!
  const before = decodeOrderCatalog([
    { ...blank, id: 'parallel-a', prerequisites: [] },
    { ...blank, id: 'parallel-b', prerequisites: [] },
  ])
  const after = decodeOrderCatalog([
    { ...blank, id: 'parallel-b', prerequisites: [] },
  ])
  return { before, after }
}

function savePort(overrides: Partial<{
  acceptOrder(): Promise<void>
  completeOrder(): Promise<number>
  acquireTool(): Promise<void>
}> = {}) {
  return {
    updateTree: async () => 1,
    insertTree: async () => 1,
    updateCamera: async () => {},
    acceptOrder: overrides.acceptOrder ?? (async () => {}),
    abandonOrder: async () => {},
    completeOrder: overrides.completeOrder ?? (async () => 1),
    setTutorialsEnabled: async () => {},
    completeTutorialMilestone: async () => {},
    acquireTool: overrides.acquireTool ?? (async () => {}),
  }
}

describe('live order catalog publication transaction', () => {
  it('flushes a queued acceptance before permanently removing its order', async () => {
    // Catches repository reconciliation overtaking an accepted-order write still queued for the same save.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    const acceptance = orders.planAccept('parallel-a', { x: 0, z: -6, yaw: 0 })
    orders.commit(orders.prepare(acceptance))
    const accepted = deferred<void>()
    const calls: string[] = []
    const writer = new SaveWriter('slot-a', savePort({
      acceptOrder: async () => {
        calls.push('accept')
        await accepted.promise
      },
    }))
    writer.acceptOrder('parallel-a', { x: 0, z: -6, yaw: 0 })
    const rendererPots: unknown[][] = []

    const publishing = publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer,
      contentClient: { save: async () => { calls.push('content') } },
      catalog,
      orders,
      renderer: { setPots: (pots) => { rendererPots.push([...pots]) } },
      isCurrent: () => true,
    })
    await Promise.resolve()
    expect(calls).toEqual(['accept'])

    accepted.resolve()
    await publishing

    expect(calls).toEqual(['accept', 'content'])
    expect(catalog.current).toBe(after)
    expect([...orders.progress.orders.keys()]).toEqual(['parallel-b'])
    expect(rendererPots).toEqual([[]])
    await writer.dispose()
  })

  it('does not persist or publish content when the queued save flush fails', async () => {
    // Catches a catalog save reconciling order IDs after an earlier lifecycle write failed.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    const writer = new SaveWriter('slot-a', savePort({
      acceptOrder: async () => { throw new Error('accept write failed') },
    }))
    writer.acceptOrder('parallel-a', { x: 0, z: -6, yaw: 0 })
    let contentCalls = 0
    let rendererCalls = 0

    await expect(publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer,
      contentClient: { save: async () => { contentCalls += 1 } },
      catalog,
      orders,
      renderer: { setPots: () => { rendererCalls += 1 } },
      isCurrent: () => true,
    })).rejects.toThrow('accept write failed')

    expect(contentCalls).toBe(0)
    expect(catalog.current).toBe(before)
    expect(orders.progress.orders.size).toBe(2)
    expect(rendererCalls).toBe(0)
  })

  it('flushes a queued completion before permanently removing its order', async () => {
    // Catches completed-order persistence being overtaken by the same editor removal race.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    const completion = deferred<number>()
    const calls: string[] = []
    const writer = new SaveWriter('slot-a', savePort({
      completeOrder: async () => {
        calls.push('complete')
        return completion.promise
      },
    }))
    writer.completeOrder('parallel-a', 0)

    const publishing = publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer,
      contentClient: { save: async () => { calls.push('content') } },
      catalog,
      orders,
      renderer: { setPots: () => {} },
      isCurrent: () => true,
    })
    await Promise.resolve()
    expect(calls).toEqual(['complete'])

    completion.resolve(1)
    await publishing

    expect(calls).toEqual(['complete', 'content'])
    expect(catalog.current).toBe(after)
    await writer.dispose()
  })

  it('does not publish into a replaced world after permanent persistence returns', async () => {
    // Catches a late editor save mutating a replacement session, live catalog, or disposed renderer.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const progress = initialOrderProgress(before.definitions)
    const orders = orderSession(progress, catalog)
    const content = deferred<void>()
    let current = true
    let rendererCalls = 0
    let saveStarted = false

    const publishing = publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer: { flushChecked: async () => {} },
      contentClient: {
        save: async () => {
          saveStarted = true
          await content.promise
        },
      },
      catalog,
      orders,
      renderer: { setPots: () => { rendererCalls += 1 } },
      isCurrent: () => current,
    })
    while (!saveStarted) await Promise.resolve()
    current = false
    content.resolve()

    await expect(publishing).rejects.toThrow(/no longer active/i)
    expect(orders.progress).toBe(progress)
    expect(catalog.current).toBe(before)
    expect(rendererCalls).toBe(0)
  })

  it('does not start permanent persistence if the world ends during its save flush', async () => {
    // Catches lifecycle invalidation being checked only after the external content side effect.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    const flush = deferred<void>()
    let current = true
    let contentCalls = 0
    const publishing = publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer: { flushChecked: () => flush.promise },
      contentClient: { save: async () => { contentCalls += 1 } },
      catalog,
      orders,
      renderer: { setPots: () => {} },
      isCurrent: () => current,
    })

    current = false
    flush.resolve()

    await expect(publishing).rejects.toThrow(/no longer active/i)
    expect(contentCalls).toBe(0)
  })

  it('keeps the active world generation usable when Main Menu shutdown fails', async () => {
    // Catches a failed save barrier invalidating a world that Pause still allows the player to resume.
    const { before, after } = revisions()
    const catalog = new LiveOrderCatalog(before)
    const orders = orderSession(initialOrderProgress(before.definitions), catalog)
    let saveFails = true
    let current = true
    const writer = new SaveWriter('slot-a', savePort({
      acquireTool: async () => {
        if (saveFails) throw new Error('disk full')
      },
    }))
    writer.acquireTool('double-cut')

    await expect(commitWorldShutdown(
      () => writer.dispose(),
      () => { current = false },
    )).rejects.toThrow('disk full')
    expect(current).toBe(true)

    saveFails = false
    writer.retry()
    await writer.flushChecked()
    let contentCalls = 0
    await publishOrderCatalogRevision({
      slotId: 'slot-a',
      candidate: after,
      writer,
      contentClient: { save: async () => { contentCalls += 1 } },
      catalog,
      orders,
      renderer: { setPots: () => {} },
      isCurrent: () => current,
    })

    expect(contentCalls).toBe(1)
    expect(catalog.current).toBe(after)
    await writer.dispose()
  })
})
