import type {
  LiveOrderCatalog,
  OrderCatalogRevision,
  OrderProgress,
} from '../src/game/orders/catalog'
import {
  serializeOrderCatalog,
  type OrderContentClient,
} from '../src/game/orders/content-client'
import {
  reconcileOrderProgress,
  type OrderSession,
} from '../src/game/orders/session'
import type { GameWorldRenderer } from '../src/game/render/world'

type CatalogPublicationRenderer = Pick<GameWorldRenderer, 'setPots'>

function assertCurrent(isCurrent: () => boolean): void {
  if (!isCurrent()) throw new Error('loaded world is no longer active')
}

export function acceptedPotsForRevision(
  progress: OrderProgress,
  revision: OrderCatalogRevision,
): Parameters<CatalogPublicationRenderer['setPots']>[0] {
  return [...progress.orders].flatMap(([orderId, state]) => {
    if (state.kind !== 'accepted') return []
    const definition = revision.byId.get(orderId)
    if (definition === undefined) throw new Error(`missing authored goal for '${orderId}'`)
    return [{ orderId, placement: state.pot, goal: definition.goal }]
  })
}

export async function publishOrderCatalogRevision(config: {
  readonly candidate: OrderCatalogRevision
  readonly contentClient: OrderContentClient
  readonly reconcileSave: (orderIds: readonly string[]) => Promise<void>
  readonly catalog: LiveOrderCatalog
  readonly orders: OrderSession
  readonly renderer: CatalogPublicationRenderer
  readonly isCurrent: () => boolean
}): Promise<void> {
  assertCurrent(config.isCurrent)
  await config.contentClient.save(serializeOrderCatalog(config.candidate))
  if (!config.isCurrent()) return

  const currentIds = new Set(config.catalog.current.definitions.map(({ id }) => id))
  const candidateIds = config.candidate.definitions.map(({ id }) => id)
  if (currentIds.size !== candidateIds.length || candidateIds.some((id) => !currentIds.has(id))) {
    await config.reconcileSave(candidateIds)
    if (!config.isCurrent()) return
  }

  const reconciled = reconcileOrderProgress(config.orders.progress, config.candidate)
  config.orders.replaceProgress(reconciled)
  config.catalog.publish(config.candidate)
  config.renderer.setPots(acceptedPotsForRevision(reconciled, config.candidate))
}
