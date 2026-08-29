import { sameDiagram } from '../../kernel/diagram/canonical/iso'
import { citeLibraryProposition, type LibraryProposition } from '../../kernel/proof/library'
import { DiagramBuilder } from '../../kernel/diagram/builder'
import {
  ORDER_CATALOG,
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

function definitionFor(orderId: string): OrderDefinition {
  const definition = ORDER_CATALOG.find((entry) => entry.id === orderId)
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

export function initialOrderProgress(catalog: readonly OrderDefinition[]): OrderProgress {
  const orders = new Map<string, OrderState>()
  for (const order of catalog) {
    if (orders.has(order.id)) throw new OrderError(`duplicate order '${order.id}'`)
    orders.set(order.id, { kind: 'pending' })
  }
  return { reputation: 0, orders }
}

export class OrderSession {
  private prepared: PreparedOrderCommit | null = null
  private readonly preparedProgress = new WeakMap<PreparedOrderCommit, OrderProgress>()

  public constructor(private currentProgress: OrderProgress) {}

  public get progress(): OrderProgress {
    return this.currentProgress
  }

  public planAccept(orderId: string, pot: PotPlacement): OrderMutation {
    definitionFor(orderId)
    const state = stateFor(this.progress, orderId)
    if (state.kind !== 'pending') throw new OrderError(`order '${orderId}' must be pending to accept`)
    return {
      kind: 'accept',
      orderId,
      pot,
      before: this.progress,
      after: withOrder(this.progress, orderId, { kind: 'accepted', pot }),
    }
  }

  public planAbandon(orderId: string): OrderMutation {
    definitionFor(orderId)
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
    const definition = definitionFor(orderId)
    const state = stateFor(this.progress, orderId)
    if (state.kind !== 'accepted') throw new OrderError(`order '${orderId}' must be accepted to deliver`)

    const blank = new DiagramBuilder().build()
    const delivered = citeLibraryProposition(blank, source, blank.root)
    if (!sameDiagram(delivered, definition.goal.diagram)) {
      throw new OrderError(`delivered proposition does not match order '${orderId}'`)
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

export function orderSession(progress: OrderProgress): OrderSession {
  return new OrderSession(progress)
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
