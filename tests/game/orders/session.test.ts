import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../../src/kernel/diagram/builder'
import { sameDiagram } from '../../../src/kernel/diagram/canonical/iso'
import { libraryProposition } from '../../../src/kernel/proof/library'
import {
  ORDER_CATALOG,
  STARTER_ORDER_ID,
} from '../../../src/game/orders/catalog'
import {
  initialOrderProgress,
  orderSession,
  publishOrderMutation,
  type OrderMutation,
} from '../../../src/game/orders/session'

const starter = ORDER_CATALOG[0]!
const acceptedPot = { x: 3, z: -6, yaw: 0.5 }

function freshSession() {
  return orderSession(initialOrderProgress(ORDER_CATALOG))
}

function acceptStarter(session = freshSession()) {
  const accepted = session.planAccept(STARTER_ORDER_ID, acceptedPot)
  session.commit(session.prepare(accepted))
  return session
}

describe('starter order catalog', () => {
  it('offers one rewarded double-cut goal', () => {
    // Catches an authored catalog that cannot supply the starter order lifecycle.
    expect(ORDER_CATALOG).toHaveLength(1)
    expect(starter).toMatchObject({
      id: 'starter-double-cut',
      reward: 1,
    })
  })
})

describe('order session lifecycle', () => {
  it('accepts the pending starter order at the chosen pot placement', () => {
    // Catches acceptance that mutates before commit or loses the placement.
    const session = freshSession()
    const accepted = session.planAccept(STARTER_ORDER_ID, acceptedPot)

    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'pending' })
    session.commit(session.prepare(accepted))
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('delivers an exactly matching whole proposition and awards its reward', () => {
    // Catches delivery that compares source identity instead of a cited whole proposition.
    const session = acceptStarter()
    const completed = session.planDelivery(
      STARTER_ORDER_ID,
      libraryProposition('source', starter.goal.diagram),
    )

    session.commit(session.prepare(completed))
    expect(session.progress.reputation).toBe(1)
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'completed' })
  })

  it('does not consume the proposition supplied for a successful delivery', () => {
    // Catches a delivery path that mutates, clears, or otherwise consumes its source proposition.
    const session = acceptStarter()
    const source = libraryProposition('source', starter.goal.diagram)
    const before = source.diagram
    const completed = session.planDelivery(STARTER_ORDER_ID, source)

    session.commit(session.prepare(completed))
    expect(source.diagram).toBe(before)
    expect(sameDiagram(source.diagram, starter.goal.diagram)).toBe(true)
  })

  it('rejects acceptance and delivery transitions that do not start from their required state', () => {
    // Catches lifecycle operations that permit parallel or skipped state transitions.
    const session = freshSession()
    expect(() => session.planDelivery(
      STARTER_ORDER_ID,
      libraryProposition('source', starter.goal.diagram),
    )).toThrow(/accepted/i)

    acceptStarter(session)
    expect(() => session.planAccept(STARTER_ORDER_ID, acceptedPot)).toThrow(/pending/i)
  })

  it('returns an accepted order to pending when it is abandoned', () => {
    // Catches abandonment that removes the order or leaves it accepted.
    const session = acceptStarter()
    const abandoned = session.planAbandon(STARTER_ORDER_ID)

    session.commit(session.prepare(abandoned))
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'pending' })
    expect(session.progress.reputation).toBe(0)
  })

  it('rejects abandoning an order that is not accepted', () => {
    // Catches abandonment that permits completed or pending orders to re-enter the lifecycle.
    const session = freshSession()
    expect(() => session.planAbandon(STARTER_ORDER_ID)).toThrow(/accepted/i)
  })

  it('retains accepted state when the delivered proposition differs from the authored goal', () => {
    // Catches delivery that accepts a merely trusted proposition without exact diagram equivalence.
    const session = acceptStarter()
    const wrong = libraryProposition('wrong', new DiagramBuilder().build())

    expect(() => session.planDelivery(STARTER_ORDER_ID, wrong)).toThrow(/does not match/i)
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('rejects repeated completion', () => {
    // Catches a completed order accruing reward again or moving through a second completion transition.
    const session = acceptStarter()
    const completed = session.planDelivery(STARTER_ORDER_ID, libraryProposition('source', starter.goal.diagram))
    session.commit(session.prepare(completed))

    expect(() => session.planDelivery(
      STARTER_ORDER_ID,
      libraryProposition('source-again', starter.goal.diagram),
    )).toThrow(/accepted/i)
    expect(session.progress).toMatchObject({ reputation: 1 })
  })

  it('rejects a prepared transition that was planned from stale progress', () => {
    // Catches prepare replacing newer progress with a transition planned from an old state.
    const session = freshSession()
    const first = session.planAccept(STARTER_ORDER_ID, acceptedPot)
    const stale = session.planAccept(STARTER_ORDER_ID, { x: 9, z: 1, yaw: 2 })
    session.commit(session.prepare(first))

    expect(() => session.prepare(stale)).toThrow(/changed since mutation was planned/i)
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'accepted', pot: acceptedPot })
  })

  it('rejects a forged completion that changes reward and removes order state', () => {
    // Catches prepare trusting public mutation.after instead of validating the catalog reward and order map.
    const session = acceptStarter()
    const before = session.progress
    const forged: OrderMutation = {
      kind: 'complete',
      orderId: STARTER_ORDER_ID,
      reward: 999,
      before,
      after: { reputation: 999, orders: new Map() },
    }

    expect(() => session.prepare(forged)).toThrow(/invalid order mutation/i)
    expect(session.progress).toBe(before)
    const abandonment = session.planAbandon(STARTER_ORDER_ID)
    session.commit(session.prepare(abandonment))
    expect(session.progress.orders.get(STARTER_ORDER_ID)).toEqual({ kind: 'pending' })
  })

  it('rejects a forged acceptance whose resulting pot differs from its mutation payload', () => {
    // Catches prepare accepting a state transition whose externally supplied after-state disagrees with it.
    const session = freshSession()
    const before = session.progress
    const orders = new Map(before.orders)
    orders.set(STARTER_ORDER_ID, { kind: 'accepted', pot: { x: 9, z: 1, yaw: 2 } })
    const forged: OrderMutation = {
      kind: 'accept',
      orderId: STARTER_ORDER_ID,
      pot: acceptedPot,
      before,
      after: { reputation: 0, orders },
    }

    expect(() => session.prepare(forged)).toThrow(/invalid order mutation/i)
    expect(session.progress).toBe(before)
  })

  it('publishes a completed order only after save acceptance and before renderer commit', () => {
    // Catches publication that exposes completed progress before persistence accepts it.
    const session = acceptStarter()
    const completion = session.planDelivery(STARTER_ORDER_ID, libraryProposition('source', starter.goal.diagram))
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
})
