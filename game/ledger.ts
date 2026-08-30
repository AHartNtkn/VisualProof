import { availableOrderIds, type OrderCatalogRevision } from '../src/game/orders/catalog'
import type { GameProgress } from '../src/game/model'
import { orderTutorialGate, toolTutorialGate, type TutorialMilestoneId } from '../src/game/tutorial'
import { TOOL_CATALOG, type ToolId, type ToolInventory } from '../src/game/tools'
import { renderDiagramPreview } from './diagram-preview'

export type LedgerView = {
  readonly eye: { readonly x: number; readonly y: number; readonly z: number }
  readonly forward: { readonly x: number; readonly y: number; readonly z: number }
}

export type LedgerState = {
  readonly catalog: OrderCatalogRevision
  readonly progress: GameProgress
  readonly tools: ToolInventory
  readonly tutorialCheck: (milestone: TutorialMilestoneId) => boolean
  readonly developerMode: boolean
  readonly view: LedgerView
}

export type LedgerActions = {
  readonly acquireTool: (toolId: ToolId) => void
  readonly acceptOrder: (orderId: string, view: LedgerView) => void
  readonly abandonOrder: (orderId: string) => void
  readonly editOrder: (orderId: string) => void
  readonly createOrder: () => void
}

export type LedgerPrimaryTab = 'tools' | 'orders'
type ToolTab = 'available' | 'acquired'
type OrderTab = 'available' | 'active' | 'completed'

export type LedgerController = {
  show(state: LedgerState): void
  hide(): void
  readonly isOpen: boolean
  readonly selectedPrimaryTab: LedgerPrimaryTab
  dispose(): void
}

function required<ElementType extends Element>(root: HTMLElement, selector: string): ElementType {
  const element = root.querySelector<ElementType>(selector)
  if (element === null) throw new Error(`missing ledger element '${selector}'`)
  return element
}

function gatePasses(
  gate: TutorialMilestoneId | null,
  tutorialCheck: (milestone: TutorialMilestoneId) => boolean,
): boolean {
  return gate === null || tutorialCheck(gate)
}

export function mountLedger(root: HTMLElement, actions: LedgerActions): LedgerController {
  const primaryHost = required<HTMLElement>(root, '[data-ledger-primary-tabs]')
  const contextHost = required<HTMLElement>(root, '[data-ledger-context-tabs]')
  const content = required<HTMLElement>(root, '[data-ledger-content]')
  const staticDisposers: Array<() => void> = []
  const renderDisposers: Array<() => void> = []
  let primary: LedgerPrimaryTab = 'tools'
  let toolsTab: ToolTab = 'available'
  let ordersTab: OrderTab = 'available'
  let current: LedgerState | null = null
  let disposed = false

  const listen = (
    target: EventTarget,
    type: string,
    listener: EventListener,
    disposers: Array<() => void>,
  ): void => {
    target.addEventListener(type, listener)
    disposers.push(() => target.removeEventListener(type, listener))
  }
  const disposeRenderedListeners = (): void => {
    while (renderDisposers.length > 0) renderDisposers.pop()!()
  }

  const primaryButtons = new Map<LedgerPrimaryTab, HTMLButtonElement>()
  for (const [name, label] of [['tools', 'Tools'], ['orders', 'Orders']] as const) {
    const button = root.ownerDocument.createElement('button')
    button.type = 'button'
    button.dataset['ledgerPrimary'] = name
    button.textContent = label
    listen(button, 'click', () => {
      if (disposed || current === null) return
      primary = name
      render()
      if (name === 'orders' && current.developerMode) actions.createOrder()
    }, staticDisposers)
    primaryButtons.set(name, button)
  }
  primaryHost.replaceChildren(...primaryButtons.values())

  const renderContextTabs = <Tab extends string>(
    tabs: readonly Tab[],
    selected: Tab,
    choose: (tab: Tab) => void,
  ): void => {
    const buttons = tabs.map((tab) => {
      const button = root.ownerDocument.createElement('button')
      button.type = 'button'
      button.dataset['ledgerContext'] = tab
      button.ariaPressed = String(tab === selected)
      button.textContent = tab[0]!.toUpperCase() + tab.slice(1)
      listen(button, 'click', () => choose(tab), renderDisposers)
      return button
    })
    contextHost.replaceChildren(...buttons)
  }

  const renderTools = (state: LedgerState): void => {
    renderContextTabs(['available', 'acquired'], toolsTab, (tab) => {
      toolsTab = tab
      render()
    })
    const acquired = new Set(state.tools.snapshotForSave())
    const definitions = TOOL_CATALOG.filter((definition) => toolsTab === 'acquired'
      ? acquired.has(definition.id)
      : !acquired.has(definition.id)
        && state.progress.reputation >= definition.capacityRequired
        && gatePasses(toolTutorialGate(definition.id), state.tutorialCheck))
    const rows = definitions.map((definition) => {
      const row = root.ownerDocument.createElement('div')
      row.className = 'ledger-tool-row'
      row.dataset['toolId'] = definition.id
      const silhouette = root.ownerDocument.createElement('span')
      silhouette.className = 'tool-silhouette ledger-tool-silhouette'
      silhouette.dataset['silhouette'] = definition.silhouette
      silhouette.style.setProperty('--tool-color', definition.color)
      const label = root.ownerDocument.createElement('span')
      label.className = 'ledger-tool-label'
      label.textContent = definition.label
      row.append(silhouette, label)
      if (toolsTab === 'available') {
        const acquire = root.ownerDocument.createElement('button')
        acquire.type = 'button'
        acquire.dataset['toolAction'] = 'acquire'
        acquire.textContent = 'Acquire'
        listen(acquire, 'click', () => actions.acquireTool(definition.id), renderDisposers)
        row.append(acquire)
      }
      return row
    })
    content.className = 'ledger-tool-rows'
    content.replaceChildren(...rows)
  }

  const renderOrders = (state: LedgerState): void => {
    renderContextTabs(['available', 'active', 'completed'], ordersTab, (tab) => {
      ordersTab = tab
      render()
    })
    const available = new Set(availableOrderIds(state.progress, state.catalog, (orderId) => (
      gatePasses(orderTutorialGate(orderId), state.tutorialCheck)
    )))
    const definitions = state.catalog.definitions.filter((definition) => {
      const orderState = state.progress.orders.get(definition.id)
      if (ordersTab === 'available') return available.has(definition.id)
      if (ordersTab === 'active') return orderState?.kind === 'accepted'
      return orderState?.kind === 'completed'
    })
    const tiles = definitions.map((definition) => {
      const orderState = state.progress.orders.get(definition.id)!
      const tile = root.ownerDocument.createElement('article')
      tile.className = 'ledger-order-tile'
      tile.dataset['orderId'] = definition.id
      const canvas = root.ownerDocument.createElement('canvas')
      canvas.width = 240
      canvas.height = 150
      canvas.dataset['diagramPreview'] = ''
      renderDiagramPreview(canvas, definition.goal)
      const action = root.ownerDocument.createElement('button')
      action.type = 'button'
      if (state.developerMode) {
        action.dataset['orderAction'] = 'edit'
        action.textContent = 'Edit'
        listen(tile, 'click', () => actions.editOrder(definition.id), renderDisposers)
      } else if (orderState.kind === 'pending') {
        action.dataset['orderAction'] = 'accept'
        action.textContent = 'Accept'
        listen(action, 'click', () => actions.acceptOrder(definition.id, state.view), renderDisposers)
      } else if (orderState.kind === 'accepted') {
        action.dataset['orderAction'] = 'abandon'
        action.textContent = 'Abandon'
        listen(action, 'click', () => actions.abandonOrder(definition.id), renderDisposers)
      } else {
        action.dataset['orderAction'] = 'completed'
        action.textContent = 'Completed'
        action.disabled = true
      }
      tile.append(canvas, action)
      return tile
    })
    content.className = 'ledger-order-tiles'
    content.replaceChildren(...tiles)
  }

  function render(): void {
    if (current === null || disposed) return
    disposeRenderedListeners()
    for (const [name, button] of primaryButtons) button.ariaPressed = String(name === primary)
    if (primary === 'tools') renderTools(current)
    else renderOrders(current)
  }

  return {
    show(state) {
      if (disposed) return
      const opening = root.hidden
      if (opening) {
        toolsTab = 'available'
        ordersTab = 'available'
      }
      current = state
      root.hidden = false
      render()
      if (opening) primaryButtons.get(primary)!.focus()
    },
    hide() {
      root.hidden = true
    },
    get isOpen() {
      return !root.hidden
    },
    get selectedPrimaryTab() {
      return primary
    },
    dispose() {
      if (disposed) return
      disposed = true
      disposeRenderedListeners()
      while (staticDisposers.length > 0) staticDisposers.pop()!()
      current = null
      root.hidden = true
    },
  }
}
