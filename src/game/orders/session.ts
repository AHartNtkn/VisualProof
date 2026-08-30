import { sameDiagram } from '../../kernel/diagram/canonical/iso'
import { citeLibraryProposition, type LibraryProposition } from '../../kernel/proof/library'
import { DiagramBuilder } from '../../kernel/diagram/builder'
import {
  MAX_REPUTATION,
  type LiveOrderCatalog,
  type OrderCatalogRevision,
  type OrderDefinition,
  type OrderProgress,
  type OrderState,
  type PotPlacement,
} from './catalog'

export type OrderMutation =
  | {
    readonly kind: 'accept'
    readonly orderId: string
    readonly pot: PotPlacement
    readonly before: OrderProgress
    readonly after: OrderProgress
  }
  | {
    readonly kind: 'abandon'
    readonly orderId: string
    readonly before: OrderProgress
    readonly after: OrderProgress
  }
  | {
    readonly kind: 'complete'
    readonly orderId: string
    readonly reward: number
    readonly before: OrderProgress
    readonly after: OrderProgress
  }

const preparedOrderCommit: unique symbol = Symbol('prepared order commit')

export type PreparedOrderCommit = {
  readonly [preparedOrderCommit]: true
}

export type OrderMutationRenderer<Prepared> = {
  prepareOrderChange(mutation: OrderMutation): Prepared
  commitOrderChange(prepared: Prepared): void
  discardOrderChange(prepared: Prepared): void
}

class OrderError extends Error {
  public constructor(message: string) {
    super(message)
    this.name = 'OrderError'
  }
}

function definitionFor(catalog: LiveOrderCatalog, orderId: string): OrderDefinition {
  const definition = catalog.definition(orderId)
  if (definition === undefined) throw new OrderError(`unknown order '${orderId}'`)
  return definition
}

function stateFor(progress: OrderProgress, orderId: string): OrderState {
  const state = progress.orders.get(orderId)
  if (state === undefined) throw new OrderError(`order '${orderId}' is missing from progress`)
  return state
}

function withOrder(progress: OrderProgress, orderId: string, state: OrderState, reputation = progress.reputation): OrderProgress {
  const orders = new Map(progress.orders)
  orders.set(orderId, state)
  return { reputation, orders }
}

function samePot(a: PotPlacement, b: PotPlacement): boolean {
  return Object.is(a.x, b.x) && Object.is(a.z, b.z) && Object.is(a.yaw, b.yaw)
}

function sameOrderState(a: OrderState | undefined, b: OrderState): boolean {
  if (a === undefined || a.kind !== b.kind) return false
  switch (a.kind) {
    case 'pending': return true
    case 'completed': return true
    case 'accepted': return b.kind === 'accepted' && samePot(a.pot, b.pot)
  }
}

function preservesOtherOrders(
  before: OrderProgress,
  after: OrderProgress,
  orderId: string,
  nextState: OrderState,
  reputation: number,
): boolean {
  if (after.reputation !== reputation || after.orders.size !== before.orders.size) return false
  for (const [id, state] of before.orders) {
    if (id === orderId) {
      if (!sameOrderState(after.orders.get(id), nextState)) return false
    } else if (after.orders.get(id) !== state) {
      return false
    }
  }
  return true
}

function isValidMutation(catalog: LiveOrderCatalog, mutation: OrderMutation): boolean {
  const definition = definitionFor(catalog, mutation.orderId)
  const state = stateFor(mutation.before, mutation.orderId)
  switch (mutation.kind) {
    case 'accept':
      return state.kind === 'pending'
        && prerequisitesComplete(mutation.before, definition)
        && preservesOtherOrders(
          mutation.before,
          mutation.after,
          mutation.orderId,
          { kind: 'accepted', pot: mutation.pot },
          mutation.before.reputation,
        )
    case 'abandon':
      return state.kind === 'accepted'
        && preservesOtherOrders(
          mutation.before,
          mutation.after,
          mutation.orderId,
          { kind: 'pending' },
          mutation.before.reputation,
        )
    case 'complete':
      return state.kind === 'accepted'
        && mutation.reward === definition.reward
        && preservesOtherOrders(
          mutation.before,
          mutation.after,
          mutation.orderId,
          { kind: 'completed' },
          mutation.before.reputation + definition.reward,
        )
  }
}

function prerequisitesComplete(progress: OrderProgress, definition: OrderDefinition): boolean {
  return definition.prerequisites.every((id) => progress.orders.get(id)?.kind === 'completed')
}

export function initialOrderProgress(catalog: readonly OrderDefinition[]): OrderProgress {
  const orders = new Map<string, OrderState>()
  for (const order of catalog) {
    if (orders.has(order.id)) throw new OrderError(`duplicate order '${order.id}'`)
    orders.set(order.id, { kind: 'pending' })
  }
  return { reputation: 0, orders }
}

export function reconcileOrderProgress(
  progress: OrderProgress,
  revision: OrderCatalogRevision,
): OrderProgress {
  const orders = new Map<string, OrderState>()
  for (const definition of revision.definitions) {
    orders.set(definition.id, progress.orders.get(definition.id) ?? { kind: 'pending' })
  }
  return { reputation: progress.reputation, orders }
}

export class OrderSession {
  private prepared: PreparedOrderCommit | null = null
  private readonly preparedProgress = new WeakMap<PreparedOrderCommit, OrderProgress>()

  public constructor(
    private currentProgress: OrderProgress,
    private readonly catalog: LiveOrderCatalog,
  ) {}

  public get progress(): OrderProgress {
    return this.currentProgress
  }

  public replaceProgress(reconciled: OrderProgress): void {
    if (this.prepared !== null) throw new OrderError('cannot replace order progress while a mutation is prepared')
    this.currentProgress = reconciled
  }

  public planAccept(orderId: string, pot: PotPlacement): OrderMutation {
    const definition = definitionFor(this.catalog, orderId)
    const state = stateFor(this.progress, orderId)
    if (state.kind !== 'pending') throw new OrderError(`order '${orderId}' must be pending to accept`)
    if (!prerequisitesComplete(this.progress, definition)) {
      throw new OrderError(`order '${orderId}' prerequisites are incomplete`)
    }
    if (![pot.x, pot.z, pot.yaw].every(Number.isFinite)) {
      throw new OrderError('order pot placement must use finite coordinates')
    }
    return {
      kind: 'accept',
      orderId,
      pot,
      before: this.progress,
      after: withOrder(this.progress, orderId, { kind: 'accepted', pot }),
    }
  }

  public planAbandon(orderId: string): OrderMutation {
    definitionFor(this.catalog, orderId)
    const state = stateFor(this.progress, orderId)
    if (state.kind !== 'accepted') throw new OrderError(`order '${orderId}' must be accepted to abandon`)
    return {
      kind: 'abandon',
      orderId,
      before: this.progress,
      after: withOrder(this.progress, orderId, { kind: 'pending' }),
    }
  }

  public planDelivery(orderId: string, source: LibraryProposition): OrderMutation {
    const definition = definitionFor(this.catalog, orderId)
    const state = stateFor(this.progress, orderId)
    if (state.kind !== 'accepted') throw new OrderError(`order '${orderId}' must be accepted to deliver`)

    const blank = new DiagramBuilder().build()
    const delivered = citeLibraryProposition(blank, source, blank.root)
    if (!sameDiagram(delivered, definition.goal.diagram)) {
      throw new OrderError(`delivered proposition does not match order '${orderId}'`)
    }
    if (this.progress.reputation > MAX_REPUTATION - definition.reward) {
      throw new OrderError('order reward would exceed the maximum reputation')
    }
    return {
      kind: 'complete',
      orderId,
      reward: definition.reward,
      before: this.progress,
      after: withOrder(this.progress, orderId, { kind: 'completed' }, this.progress.reputation + definition.reward),
    }
  }

  public prepare(mutation: OrderMutation): PreparedOrderCommit {
    if (this.prepared !== null) throw new OrderError('order mutation publication is already prepared')
    if (this.progress !== mutation.before) {
      throw new OrderError(`order '${mutation.orderId}' changed since mutation was planned`)
    }
    if (!isValidMutation(this.catalog, mutation)) throw new OrderError('invalid order mutation')
    const prepared: PreparedOrderCommit = { [preparedOrderCommit]: true }
    this.prepared = prepared
    this.preparedProgress.set(prepared, mutation.after)
    return prepared
  }

  public commit(prepared: PreparedOrderCommit): void {
    if (this.prepared !== prepared) return
    const progress = this.preparedProgress.get(prepared)
    if (progress === undefined) return
    this.prepared = null
    this.preparedProgress.delete(prepared)
    this.currentProgress = progress
  }

  public discard(prepared: PreparedOrderCommit): void {
    if (this.prepared === prepared) {
      this.prepared = null
      this.preparedProgress.delete(prepared)
    }
  }
}

export function orderSession(progress: OrderProgress, catalog: LiveOrderCatalog): OrderSession {
  return new OrderSession(progress, catalog)
}

export function publishOrderMutation<Prepared>(
  session: OrderSession,
  mutation: OrderMutation,
  renderer: OrderMutationRenderer<Prepared>,
  acceptSave: (mutation: OrderMutation) => void,
): void {
  const preparedSession = session.prepare(mutation)
  let preparedRenderer: Prepared
  try {
    preparedRenderer = renderer.prepareOrderChange(mutation)
  } catch (error) {
    session.discard(preparedSession)
    throw error
  }
  try {
    acceptSave(mutation)
  } catch (error) {
    try {
      renderer.discardOrderChange(preparedRenderer)
    } catch {
      // The save-acceptance error is authoritative; renderer cleanup must not mask it.
    } finally {
      session.discard(preparedSession)
    }
    throw error
  }
  session.commit(preparedSession)
  renderer.commitOrderChange(preparedRenderer)
}
