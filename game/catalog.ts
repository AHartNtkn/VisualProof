import type { OrderDefinition, OrderProgress } from '../src/game/orders/catalog'
import type { EquippedItem } from '../src/game/tools'

export type CatalogView = {
  readonly eye: { readonly x: number; readonly y: number; readonly z: number }
  readonly forward: { readonly x: number; readonly y: number; readonly z: number }
}

export type CatalogActions = {
  readonly accept: (orderId: string, view: CatalogView) => void
  readonly abandon: (orderId: string) => void
}

export type CatalogController = {
  show(progress: OrderProgress, view: CatalogView): void
  hide(): void
  dispose(): void
}

type CatalogTab = 'pending' | 'completed'

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing catalog element '${selector}'`)
  return element
}

export function renderEquippedItem(root: HTMLElement, item: EquippedItem, cuttingHeld: boolean): void {
  const silhouette = required<HTMLElement>(root, '[data-equipped-silhouette]')
  const label = required<HTMLElement>(root, '[data-equipped-item-label]')
  const held = required<HTMLElement>(root, '[data-held-cutting]')
  silhouette.dataset['item'] = item
  label.textContent = item === 'double-cut' ? 'Double Cut' : 'Iteration'
  held.textContent = cuttingHeld ? 'Cutting held' : 'No cutting held'
}

export function mountCatalog(
  root: HTMLElement,
  definitions: readonly OrderDefinition[],
  actions: CatalogActions,
): CatalogController {
  const pending = required<HTMLButtonElement>(root, '[data-catalog-pending]')
  const completed = required<HTMLButtonElement>(root, '[data-catalog-completed]')
  const reputation = required<HTMLElement>(root, '[data-catalog-reputation]')
  const orders = required<HTMLElement>(root, '[data-catalog-orders]')
  const staticDisposers: Array<() => void> = []
  const orderDisposers: Array<() => void> = []
  let tab: CatalogTab = 'pending'
  let current: OrderProgress | null = null
  let capturedView: CatalogView | null = null

  const listen = (
    target: EventTarget,
    type: string,
    listener: EventListener,
    disposers: Array<() => void>,
  ): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const disposeOrderActions = (): void => {
    while (orderDisposers.length > 0) orderDisposers.pop()!()
  }
  const render = (): void => {
    if (current === null) return
    disposeOrderActions()
    pending.ariaPressed = String(tab === 'pending')
    completed.ariaPressed = String(tab === 'completed')
    reputation.textContent = `Reputation: ${current.reputation}`
    const cards: HTMLElement[] = []
    for (const definition of definitions) {
      const state = current.orders.get(definition.id)
      if (state === undefined) continue
      if ((tab === 'completed') !== (state.kind === 'completed')) continue
      const card = root.ownerDocument.createElement('article')
      const title = root.ownerDocument.createElement('strong')
      const description = root.ownerDocument.createElement('p')
      title.textContent = definition.title
      description.textContent = definition.description
      card.append(title, description)
      if (state.kind === 'pending') {
        const accept = root.ownerDocument.createElement('button')
        accept.type = 'button'
        accept.dataset['catalogAccept'] = definition.id
        accept.textContent = 'Accept'
        listen(accept, 'click', () => {
          if (capturedView !== null) actions.accept(definition.id, capturedView)
        }, orderDisposers)
        card.append(accept)
      } else if (state.kind === 'accepted') {
        const abandon = root.ownerDocument.createElement('button')
        abandon.type = 'button'
        abandon.dataset['catalogAbandon'] = definition.id
        abandon.textContent = 'Abandon'
        listen(abandon, 'click', () => actions.abandon(definition.id), orderDisposers)
        card.append(abandon)
      }
      cards.push(card)
    }
    orders.replaceChildren(...cards)
  }

  listen(pending, 'click', () => {
    tab = 'pending'
    render()
  }, staticDisposers)
  listen(completed, 'click', () => {
    tab = 'completed'
    render()
  }, staticDisposers)
  listen(root, 'keydown', (event) => {
    if (!root.hidden && (event as KeyboardEvent).code === 'Tab') event.stopPropagation()
  }, staticDisposers)

  return {
    show(progress, view) {
      current = progress
      capturedView = view
      root.hidden = false
      render()
      pending.focus()
    },
    hide() {
      root.hidden = true
    },
    dispose() {
      disposeOrderActions()
      while (staticDisposers.length > 0) staticDisposers.pop()!()
      current = null
      capturedView = null
    },
  }
}
