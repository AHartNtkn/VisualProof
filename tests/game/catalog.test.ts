import { describe, expect, it } from 'vitest'
import { mountCatalog, renderEquippedItem } from '../../game/catalog'
import { ORDER_CATALOG, type OrderDefinition, type OrderProgress } from '../../src/game/orders/catalog'

const starterOrder = ORDER_CATALOG[0]!

class TestElement extends EventTarget {
  public textContent = ''
  public hidden = false
  public type = ''
  public className = ''
  public ariaPressed = 'false'
  public focusCalls = 0
  public parent: EventTarget | null = null
  public readonly dataset: Record<string, string> = {}
  public readonly children: TestElement[] = []

  public constructor(public readonly ownerDocument: TestDocument) {
    super()
  }

  public append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  public replaceChildren(...children: TestElement[]): void {
    for (const child of this.children) child.parent = null
    for (const child of children) child.parent = this
    this.children.splice(0, this.children.length, ...children)
  }

  public focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  public override dispatchEvent(event: Event): boolean {
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }

  public querySelector<T extends Element>(selector: string): T | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as T
    for (const child of this.children) {
      const found = child.querySelector<T>(selector)
      if (found !== null) return found
    }
    return null
  }
}

class TestDocument {
  public activeElement: TestElement | null = null

  public createElement(_tagName: string): TestElement {
    return new TestElement(this)
  }
}

function element(documentTarget: TestDocument, selector: string): TestElement {
  const target = documentTarget.createElement('div')
  const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
  if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
  target.dataset[key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())] = ''
  return target
}

function progress(state: 'pending' | 'accepted' | 'completed', reputation = 0): OrderProgress {
  return {
    reputation,
    orders: new Map([[starterOrder.id, state === 'accepted'
      ? { kind: 'accepted' as const, pot: { x: 2, z: -4, yaw: 0.25 } }
      : { kind: state }]]),
  }
}

function catalogHarness(): {
  readonly root: TestElement
  readonly pending: TestElement
  readonly completed: TestElement
  readonly reputation: TestElement
  readonly orders: TestElement
  readonly global: EventTarget
  readonly accepts: Array<{ readonly orderId: string; readonly view: object }>
  readonly abandoned: string[]
  readonly controller: ReturnType<typeof mountCatalog>
} {
  const documentTarget = new TestDocument()
  const root = element(documentTarget, '[data-catalog]')
  const global = new EventTarget()
  root.parent = global
  const pending = element(documentTarget, '[data-catalog-pending]')
  const completed = element(documentTarget, '[data-catalog-completed]')
  const reputation = element(documentTarget, '[data-catalog-reputation]')
  const orders = element(documentTarget, '[data-catalog-orders]')
  root.append(pending, completed, reputation, orders)
  const accepts: Array<{ readonly orderId: string; readonly view: object }> = []
  const abandoned: string[] = []
  const controller = mountCatalog(root as unknown as HTMLElement, ORDER_CATALOG as readonly OrderDefinition[], {
    accept: (orderId, view) => accepts.push({ orderId, view }),
    abandon: (orderId) => abandoned.push(orderId),
  })
  return { root, pending, completed, reputation, orders, global, accepts, abandoned, controller }
}

function action(card: TestElement, name: 'accept' | 'abandon'): TestElement | null {
  return actions(card, name)[0] ?? null
}

function actions(card: TestElement, name: 'accept' | 'abandon'): readonly TestElement[] {
  const key = `catalog${name[0]!.toUpperCase()}${name.slice(1)}`
  return card.children.filter((child) => Object.hasOwn(child.dataset, key))
}

function onlyOrder(orders: TestElement): TestElement {
  const order = orders.children[0]
  if (order === undefined) throw new Error('expected one rendered order')
  return order
}

describe('catalog controller', () => {
  it('focuses the first catalog filter when shown', () => {
    const harness = catalogHarness()

    harness.controller.show(progress('pending'), { eye: { x: 0, y: 0, z: 0 }, forward: { x: 0, y: 0, z: -1 } })

    expect(harness.pending.focusCalls).toBe(1)
  })

  it('keeps catalog Tab navigation local until its listener is disposed', () => {
    const harness = catalogHarness()
    let globalToggles = 0
    harness.global.addEventListener('keydown', () => { globalToggles += 1 })
    harness.controller.show(progress('pending'), { eye: { x: 0, y: 0, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    const tab = Object.defineProperty(new Event('keydown', { bubbles: true, cancelable: true }), 'code', { value: 'Tab' })

    harness.pending.dispatchEvent(tab)

    expect(globalToggles).toBe(0)
    expect(tab.defaultPrevented).toBe(false)

    harness.controller.dispose()
    const releasedTab = Object.defineProperty(new Event('keydown', { bubbles: true, cancelable: true }), 'code', { value: 'Tab' })
    harness.pending.dispatchEvent(releasedTab)

    expect(globalToggles).toBe(1)
    expect(releasedTab.defaultPrevented).toBe(false)
  })

  it('projects pending and completed orders into the selected tab with one state-appropriate action', () => {
    const harness = catalogHarness()
    const view = { eye: { x: 3, y: 1.7, z: 5 }, forward: { x: 0, y: 0, z: -1 } }

    harness.controller.show(progress('pending', 4), view)

    expect(harness.root.hidden).toBe(false)
    expect(harness.pending.ariaPressed).toBe('true')
    expect(harness.completed.ariaPressed).toBe('false')
    expect(harness.reputation.textContent).toBe('Reputation: 4')
    expect(harness.orders.children).toHaveLength(1)
    expect(actions(onlyOrder(harness.orders), 'accept')).toHaveLength(1)
    expect(actions(onlyOrder(harness.orders), 'abandon')).toHaveLength(0)

    const accept = action(onlyOrder(harness.orders), 'accept')!
    harness.completed.dispatchEvent(new Event('click'))
    expect(harness.pending.ariaPressed).toBe('false')
    expect(harness.completed.ariaPressed).toBe('true')
    expect(harness.orders.children).toHaveLength(0)
    accept.dispatchEvent(new Event('click'))
    expect(harness.accepts).toEqual([])

    harness.controller.show(progress('accepted', 4), view)
    harness.pending.dispatchEvent(new Event('click'))
    expect(harness.orders.children).toHaveLength(1)
    expect(actions(onlyOrder(harness.orders), 'accept')).toHaveLength(0)
    expect(actions(onlyOrder(harness.orders), 'abandon')).toHaveLength(1)
    action(onlyOrder(harness.orders), 'abandon')!.dispatchEvent(new Event('click'))
    expect(harness.abandoned).toEqual([starterOrder.id])

    harness.controller.show(progress('completed', 5), view)
    harness.completed.dispatchEvent(new Event('click'))
    expect(harness.orders.children).toHaveLength(1)
    expect(actions(onlyOrder(harness.orders), 'accept')).toHaveLength(0)
    expect(actions(onlyOrder(harness.orders), 'abandon')).toHaveLength(0)
  })

  it('delivers the view captured when shown to a pending order acceptance', () => {
    const harness = catalogHarness()
    const view = { eye: { x: 3, y: 1.7, z: 5 }, forward: { x: 0, y: 0, z: -1 } }
    harness.controller.show(progress('pending'), view)

    action(onlyOrder(harness.orders), 'accept')!.dispatchEvent(new Event('click'))

    expect(harness.accepts).toEqual([{ orderId: starterOrder.id, view }])
  })

  it('detaches tabs and current order actions on disposal', () => {
    const harness = catalogHarness()
    harness.controller.show(progress('accepted'), { eye: { x: 0, y: 0, z: 0 }, forward: { x: 0, y: 0, z: -1 } })
    const abandon = action(onlyOrder(harness.orders), 'abandon')!
    harness.controller.dispose()

    harness.pending.dispatchEvent(new Event('click'))
    harness.completed.dispatchEvent(new Event('click'))
    abandon.dispatchEvent(new Event('click'))

    expect(harness.pending.ariaPressed).toBe('true')
    expect(harness.completed.ariaPressed).toBe('false')
    expect(harness.abandoned).toEqual([])
  })
})

describe('equipped item display', () => {
  it('projects both functional item labels and the held-cutting state', () => {
    const documentTarget = new TestDocument()
    const root = documentTarget.createElement('div')
    const silhouette = element(documentTarget, '[data-equipped-silhouette]')
    const label = element(documentTarget, '[data-equipped-item-label]')
    const held = element(documentTarget, '[data-held-cutting]')
    root.append(silhouette, label, held)

    renderEquippedItem(root as unknown as HTMLElement, 'double-cut', false)
    expect(label.textContent).toBe('Double Cut')
    expect(silhouette.dataset.item).toBe('double-cut')
    expect(held.textContent).toBe('No cutting held')

    renderEquippedItem(root as unknown as HTMLElement, 'iteration', true)
    expect(label.textContent).toBe('Iteration')
    expect(silhouette.dataset.item).toBe('iteration')
    expect(held.textContent).toBe('Cutting held')
  })
})
