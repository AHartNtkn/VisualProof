import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { libraryProposition } from '../../../src/kernel/proof/library'
import {
  LiveOrderCatalog,
  MAX_REPUTATION,
  decodeOrderCatalog,
  openingOrderCatalog,
  type OrderProgress,
} from '../../../src/game/orders/catalog'
import {
  initialOrderProgress,
  orderSession,
  publishOrderMutation,
  reconcileOrderProgress,
  type OrderMutation,
} from '../../../src/game/orders/session'

const openingOrderContent: unknown = JSON.parse(readFileSync(
  new URL('../../../game/content/orders.json', import.meta.url),
  'utf8',
))
const orderId = 'blank-sprout'
const starter = openingOrderCatalog.definition(orderId)!
const acceptedPot = { x: 3, z: -6, yaw: 0.5 }

function freshCatalog(): LiveOrderCatalog {
  return new LiveOrderCatalog(openingOrderCatalog.current)
}

function freshSession(catalog = freshCatalog()) {
  return orderSession(initialOrderProgress(catalog.current.definitions), catalog)
}

function acceptStarter(session = freshSession()) {
  const accepted = session.planAccept(orderId, acceptedPot)
  session.commit(session.prepare(accepted))
  return session
}

describe('order session lifecycle', () => {
  it('uses its supplied live catalog for pending acceptance and exact delivery', () => {
    // Catches session transitions reading a static catalog rather than the injected live authority.
    const catalog = freshCatalog()
    const session = freshSession(catalog)
    const accepted = session.planAccept(orderId, acceptedPot)

    session.commit(session.prepare(accepted))
    const completed = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    session.commit(session.prepare(completed))

    expect(session.progress.reputation).toBe(1)
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'completed' })
  })

  it('rejects non-finite pot placement before planning any live acceptance', () => {
    // Catches invalid placement values entering live order state before the save boundary rejects them.
    const session = freshSession()
    for (const pot of [
      { x: Number.NaN, z: 0, yaw: 0 },
      { x: 0, z: Number.POSITIVE_INFINITY, yaw: 0 },
      { x: 0, z: 0, yaw: Number.NEGATIVE_INFINITY },
    ]) {
      expect(() => session.planAccept(orderId, pot)).toThrow(/finite/i)
      expect(session.progress.orders.get(orderId)).toEqual({ kind: 'pending' })
    }
  })

  it('rejects completion when its reward would exceed the wire reputation range', () => {
    // Catches live completion and durable enqueue occurring for a reputation the wire cannot represent.
    const catalog = freshCatalog()
    const progress = initialOrderProgress(catalog.current.definitions)
    const session = orderSession({ ...progress, reputation: MAX_REPUTATION }, catalog)
    const accepted = session.planAccept(orderId, acceptedPot)
    session.commit(session.prepare(accepted))

    expect(() => session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram)))
      .toThrow(/reputation/i)
    expect(session.progress.reputation).toBe(MAX_REPUTATION)
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('retains accepted state when the delivered proposition differs from the authored goal', () => {
    // Catches delivery accepting a merely trusted proposition without exact diagram equivalence.
    const session = acceptStarter()
    const wrong = libraryProposition(
      'wrong',
      openingOrderCatalog.definition('single-double-cut')!.goal.diagram,
    )

    expect(() => session.planDelivery(orderId, wrong)).toThrow(/does not match/i)
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('requires each lifecycle transition to start from its required state', () => {
    // Catches acceptance, abandonment, or completion skipping the order state machine.
    const session = freshSession()
    expect(() => session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))).toThrow(/accepted/i)
    expect(() => session.planAbandon(orderId)).toThrow(/accepted/i)

    acceptStarter(session)
    expect(() => session.planAccept(orderId, acceptedPot)).toThrow(/pending/i)
  })

  it('returns an accepted order to pending when it is abandoned', () => {
    // Catches abandonment removing the order or leaving it accepted.
    const session = acceptStarter()
    const abandoned = session.planAbandon(orderId)

    session.commit(session.prepare(abandoned))
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'pending' })
    expect(session.progress.reputation).toBe(0)
  })

  it('rejects repeated completion', () => {
    // Catches a completed order accruing reward again or moving through a second completion transition.
    const session = acceptStarter()
    const completed = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    session.commit(session.prepare(completed))

    expect(() => session.planDelivery(orderId, libraryProposition('source-again', starter.goal.diagram)))
      .toThrow(/accepted/i)
    expect(session.progress).toMatchObject({ reputation: 1 })
  })

  it('rejects a prepared transition planned from stale progress', () => {
    // Catches prepare replacing newer progress with a mutation planned from an earlier state.
    const session = freshSession()
    const first = session.planAccept(orderId, acceptedPot)
    const stale = session.planAccept(orderId, { x: 9, z: 1, yaw: 2 })
    session.commit(session.prepare(first))

    expect(() => session.prepare(stale)).toThrow(/changed since mutation was planned/i)
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('revalidates delivery reward against a newer catalog revision before commit', () => {
    // Catches a prepared completion awarding the reward that was valid only when it was planned.
    const catalog = freshCatalog()
    const session = acceptStarter(orderSession(initialOrderProgress(catalog.current.definitions), catalog))
    const completion = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    const content = structuredClone(openingOrderContent) as Array<Record<string, unknown>>
    content[0]!['reward'] = 2

    catalog.publish(decodeOrderCatalog(content))

    expect(() => session.prepare(completion)).toThrow(/invalid order mutation/i)
    expect(session.progress.orders.get(orderId)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('reconciles progress by preserving shared ids, adding new ids, and removing absent ids', () => {
    // Catches live revision replacement losing shared order state or retaining deleted order state.
    const progress: OrderProgress = {
      reputation: 3,
      orders: new Map([
        ['blank-sprout', { kind: 'completed' as const }],
        ['obsolete', { kind: 'pending' as const }],
      ]),
    }

    const reconciled = reconcileOrderProgress(progress, openingOrderCatalog.current)

    expect(reconciled.reputation).toBe(3)
    expect([...reconciled.orders]).toEqual([
      ['blank-sprout', { kind: 'completed' }],
      ['single-double-cut', { kind: 'pending' }],
      ['irregular-double-cut-a', { kind: 'pending' }],
      ['irregular-double-cut-b', { kind: 'pending' }],
    ])
  })

  it('rejects live progress replacement while a mutation is prepared', () => {
    // Catches revision reconciliation replacing the state that an in-flight mutation will commit from.
    const catalog = freshCatalog()
    const session = freshSession(catalog)
    const mutation = session.planAccept(orderId, acceptedPot)
    session.prepare(mutation)

    expect(() => session.replaceProgress(reconcileOrderProgress(session.progress, catalog.current)))
      .toThrow(/prepared/i)
  })

  it('does not consume the proposition supplied for a successful delivery', () => {
    // Catches a delivery path that mutates, clears, or otherwise consumes its source proposition.
    const session = acceptStarter()
    const source = libraryProposition('source', starter.goal.diagram)
    const before = source.diagram
    const completed = session.planDelivery(orderId, source)

    session.commit(session.prepare(completed))
    expect(source.diagram).toBe(before)
    expect(sameDiagram(source.diagram, starter.goal.diagram)).toBe(true)
  })

  it('rejects forged completions that change reward or remove order state', () => {
    // Catches prepare trusting public mutation.after instead of validating the current catalog and order map.
    const session = acceptStarter()
    const before = session.progress
    const forged: OrderMutation = {
      kind: 'complete',
      orderId,
      reward: 999,
      before,
      after: { reputation: 999, orders: new Map() },
    }

    expect(() => session.prepare(forged)).toThrow(/invalid order mutation/i)
    expect(session.progress).toBe(before)
  })

  it('rejects a forged acceptance whose pot differs from its mutation payload', () => {
    // Catches prepare accepting an after-state that disagrees with the acceptance payload.
    const session = freshSession()
    const before = session.progress
    const orders = new Map(before.orders)
    orders.set(orderId, { kind: 'accepted', pot: { x: 9, z: 1, yaw: 2 } })
    const forged: OrderMutation = {
      kind: 'accept',
      orderId,
      pot: acceptedPot,
      before,
      after: { reputation: 0, orders },
    }

    expect(() => session.prepare(forged)).toThrow(/invalid order mutation/i)
    expect(session.progress).toBe(before)
  })

  it('publishes a completed order only after save acceptance and before renderer commit', () => {
    // Catches publication exposing completed progress before persistence accepts it.
    const session = acceptStarter()
    const completion = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    const effects: string[] = []

    publishOrderMutation(session, completion, {
      prepareOrderChange() { effects.push('renderer-prepare'); return {} },
      commitOrderChange() {
        expect(session.progress).toBe(completion.after)
        effects.push('renderer-commit')
      },
      discardOrderChange() { effects.push('renderer-discard') },
    }, () => {
      expect(session.progress).toBe(completion.before)
      effects.push('save-accept')
    })

    expect(effects).toEqual(['renderer-prepare', 'save-accept', 'renderer-commit'])
  })

  it('leaves an accepted order authoritative when completion renderer preparation fails', () => {
    // Catches completion publication retaining prepared progress after renderer preparation rejects.
    const session = acceptStarter()
    const completion = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    const preparationError = new Error('renderer could not prepare completion')
    const effects: string[] = []

    expect(() => publishOrderMutation(session, completion, {
      prepareOrderChange() { effects.push('renderer-prepare'); throw preparationError },
      commitOrderChange() { effects.push('renderer-commit') },
      discardOrderChange() { effects.push('renderer-discard') },
    }, () => { effects.push('save-accept') })).toThrow(preparationError)

    expect(effects).toEqual(['renderer-prepare'])
    expect(session.progress).toBe(completion.before)
    expect(() => session.prepare(completion)).not.toThrow()
  })

  it('preserves completion writer rejection when renderer cleanup also fails', () => {
    // Catches completion cleanup masking the writer rejection or awarding reputation.
    const session = acceptStarter()
    const completion = session.planDelivery(orderId, libraryProposition('source', starter.goal.diagram))
    const writerError = new Error('completion writer rejected')
    const effects: string[] = []

    expect(() => publishOrderMutation(session, completion, {
      prepareOrderChange() { effects.push('renderer-prepare'); return {} },
      commitOrderChange() { effects.push('renderer-commit') },
      discardOrderChange() {
        effects.push('renderer-discard')
        throw new Error('renderer completion cleanup failed')
      },
    }, () => {
      effects.push('save-accept')
      throw writerError
    })).toThrow(writerError)

    expect(effects).toEqual(['renderer-prepare', 'save-accept', 'renderer-discard'])
    expect(session.progress).toBe(completion.before)
    expect(session.progress.reputation).toBe(0)
    expect(() => session.prepare(completion)).not.toThrow()
  })
})
