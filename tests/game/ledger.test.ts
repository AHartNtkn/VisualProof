import { describe, expect, it } from 'vitest'
import { mountLedger, type LedgerState } from '../../game/ledger'
import { openingOrderCatalog, type OrderState } from '../../src/game/orders/catalog'
import type { GameProgress } from '../../src/game/model'
import { ToolInventory } from '../../src/game/tools'
import {
  decodeToolContent,
  openingToolContent,
} from '../../src/game/tools/content'

class TestElement extends EventTarget {
  public textContent = ''
  public hidden = false
  public type = ''
  public className = ''
  public ariaPressed = 'false'
  public disabled = false
  public width = 240
  public height = 150
  public focusCalls = 0
  public previewRendered = false
  public parent: EventTarget | null = null
  public readonly dataset: Record<string, string> = {}
  public readonly children: TestElement[] = []
  public readonly style = {
    values: new Map<string, string>(),
    setProperty: (name: string, value: string): void => { this.style.values.set(name, value) },
  }

  public constructor(
    public readonly ownerDocument: TestDocument,
    public readonly tagName: string,
  ) {
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

  public getContext(kind: string): CanvasRenderingContext2D | null {
    if (kind !== '2d') return null
    return {
      clearRect() {}, beginPath() {}, moveTo() {}, lineTo() {},
      stroke: () => { this.previewRendered = true },
      save() {}, restore() {},
    } as unknown as CanvasRenderingContext2D
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

  public createElement(tagName: string): TestElement {
    return new TestElement(this, tagName.toUpperCase())
  }
}

function element(documentTarget: TestDocument, dataName: string, tagName = 'div'): TestElement {
  const target = documentTarget.createElement(tagName)
  target.dataset[dataName] = ''
  return target
}

function descendants(root: TestElement): readonly TestElement[] {
  return root.children.flatMap((child) => [child, ...descendants(child)])
}

function byData(root: TestElement, key: string, value?: string): readonly TestElement[] {
  return descendants(root).filter((candidate) => (
    Object.hasOwn(candidate.dataset, key) && (value === undefined || candidate.dataset[key] === value)
  ))
}

function progress(
  states: Readonly<Record<string, OrderState>> = {},
  reputation = 0,
  acquiredToolIds: readonly string[] = ['sprout-spawner'],
): GameProgress {
  return {
    reputation,
    orders: new Map(openingOrderCatalog.current.definitions.map((definition) => [
      definition.id,
      states[definition.id] ?? { kind: 'pending' },
    ])),
    tutorialsEnabled: true,
    completedTutorialMilestones: new Set(),
    acquiredToolIds: new Set(acquiredToolIds),
  }
}

const view = {
  eye: { x: 3, y: 1.7, z: 5 },
  forward: { x: 0, y: 0, z: -1 },
}

function harness(): {
  readonly root: TestElement
  readonly primary: TestElement
  readonly context: TestElement
  readonly content: TestElement
  readonly calls: {
    acquired: string[]
    accepted: Array<{ orderId: string; view: typeof view }>
    abandoned: string[]
    edited: string[]
    editedTools: string[]
    created: number
  }
  readonly controller: ReturnType<typeof mountLedger>
} {
  const documentTarget = new TestDocument()
  const root = element(documentTarget, 'ledger')
  root.hidden = true
  const primary = element(documentTarget, 'ledgerPrimaryTabs', 'nav')
  const context = element(documentTarget, 'ledgerContextTabs', 'nav')
  const content = element(documentTarget, 'ledgerContent')
  root.append(primary, context, content)
  const calls = {
    acquired: [] as string[],
    accepted: [] as Array<{ orderId: string; view: typeof view }>,
    abandoned: [] as string[],
    edited: [] as string[],
    editedTools: [] as string[],
    created: 0,
  }
  const controller = mountLedger(root as unknown as HTMLElement, {
    acquireTool: (toolId) => calls.acquired.push(toolId),
    acceptOrder: (orderId, acceptedView) => calls.accepted.push({ orderId, view: acceptedView }),
    abandonOrder: (orderId) => calls.abandoned.push(orderId),
    editOrder: (orderId) => calls.edited.push(orderId),
    editTool: (toolId) => calls.editedTools.push(toolId),
    createOrder: () => { calls.created += 1 },
  })
  return { root, primary, context, content, calls, controller }
}

function state(overrides: Partial<LedgerState> = {}): LedgerState {
  const gameProgress = progress()
  return {
    catalog: openingOrderCatalog.current,
    toolContent: openingToolContent.current,
    progress: gameProgress,
    tools: new ToolInventory(gameProgress.acquiredToolIds),
    tutorialCheck: () => true,
    developerMode: false,
    view,
    ...overrides,
  }
}

function click(target: TestElement): void {
  target.dispatchEvent(new Event('click', { bubbles: true }))
}

function primaryTab(root: TestElement, name: 'tools' | 'orders'): TestElement {
  return byData(root, 'ledgerPrimary', name)[0]!
}

function contextTab(root: TestElement, name: string): TestElement {
  return byData(root, 'ledgerContext', name)[0]!
}

describe('ledger controller', () => {
  it('renders current names and descriptions in Available and Acquired tool views', () => {
    // Catches either tool view substituting mechanics copy or omitting authored descriptions.
    const h = harness()
    const content = decodeToolContent(openingToolContent.current.definitions.map((definition) => ({
      ...definition,
      name: `${definition.id} live name`,
      description: `${definition.id} live description`,
    })))
    const gameProgress = progress({}, 0, ['sprout-spawner'])
    h.controller.show(state({
      toolContent: content,
      progress: gameProgress,
      tools: new ToolInventory(gameProgress.acquiredToolIds),
    }))

    const available = byData(h.content, 'toolId', 'double-cut')[0]!
    expect(available.querySelector<HTMLElement>('[data-tool-name]')?.textContent)
      .toBe('double-cut live name')
    expect(available.querySelector<HTMLElement>('[data-tool-description]')?.textContent)
      .toBe('double-cut live description')

    click(contextTab(h.root, 'acquired'))
    const acquired = byData(h.content, 'toolId', 'sprout-spawner')[0]!
    expect(acquired.querySelector<HTMLElement>('[data-tool-name]')?.textContent)
      .toBe('sprout-spawner live name')
    expect(acquired.querySelector<HTMLElement>('[data-tool-description]')?.textContent)
      .toBe('sprout-spawner live description')
  })

  it('opens tool editing from both developer tool views without acquiring', () => {
    // Catches row clicks preserving the normal acquisition side effect in developer mode.
    const h = harness()
    const gameProgress = progress({}, 0, ['sprout-spawner'])
    h.controller.show(state({
      developerMode: true,
      progress: gameProgress,
      tools: new ToolInventory(gameProgress.acquiredToolIds),
    }))

    click(byData(h.content, 'toolId', 'double-cut')[0]!)
    click(contextTab(h.root, 'acquired'))
    click(byData(h.content, 'toolId', 'sprout-spawner')[0]!)

    expect(h.calls.editedTools).toEqual(['double-cut', 'sprout-spawner'])
    expect(h.calls.acquired).toEqual([])
    expect(byData(h.content, 'toolAction', 'acquire')).toHaveLength(0)
  })
  it('projects tool rows through ownership, capacity, and tutorial gates', () => {
    // Catches owned, over-capacity, or tutorial-locked tools leaking into Available.
    const h = harness()
    const gameProgress = progress({}, 0, ['sprout-spawner'])
    h.controller.show(state({
      progress: gameProgress,
      tools: new ToolInventory(gameProgress.acquiredToolIds),
      tutorialCheck: (milestone) => milestone === 'spawn-two-sprouts',
    }))

    expect(byData(h.content, 'toolId').map(({ dataset }) => dataset['toolId'])).toEqual(['double-cut'])
    click(contextTab(h.root, 'acquired'))
    expect(byData(h.content, 'toolId').map(({ dataset }) => dataset['toolId'])).toEqual(['sprout-spawner'])
  })

  it('projects orders into available, active, and completed without exposing locked or finished work', () => {
    // Catches unmet prerequisites, tutorial gates, or accepted/completed orders leaking into Available.
    const h = harness()
    const gameProgress = progress({
      'blank-sprout': { kind: 'completed' },
      'single-double-cut': { kind: 'accepted', pot: { x: 0, z: 0, yaw: 0 } },
      'irregular-double-cut-a': { kind: 'completed' },
    })
    h.controller.show(state({
      progress: gameProgress,
      tools: new ToolInventory(gameProgress.acquiredToolIds),
      tutorialCheck: () => false,
    }))
    click(primaryTab(h.root, 'orders'))

    expect(byData(h.content, 'orderId')).toHaveLength(0)
    click(contextTab(h.root, 'active'))
    expect(byData(h.content, 'orderId').map(({ dataset }) => dataset['orderId'])).toEqual(['single-double-cut'])
    click(contextTab(h.root, 'completed'))
    expect(byData(h.content, 'orderId').map(({ dataset }) => dataset['orderId'])).toEqual([
      'blank-sprout', 'irregular-double-cut-a',
    ])
  })

  it('renders available orders only after prerequisite and tutorial checks pass', () => {
    // Catches the order projection bypassing either availability authority.
    const h = harness()
    const gameProgress = progress({ 'blank-sprout': { kind: 'completed' } })
    h.controller.show(state({
      progress: gameProgress,
      tools: new ToolInventory(gameProgress.acquiredToolIds),
      tutorialCheck: () => true,
    }))
    click(primaryTab(h.root, 'orders'))

    expect(byData(h.content, 'orderId').map(({ dataset }) => dataset['orderId'])).toEqual(['single-double-cut'])
  })

  it('renders each order tile as one visible preview and one state action without extra copy', () => {
    // Mutation caught: a title, reward, recommendation, filter, or extra action becomes visible in a tile.
    const h = harness()
    h.controller.show(state())
    click(primaryTab(h.root, 'orders'))
    const tile = byData(h.content, 'orderId')[0]!

    const descendantsOfTile = descendants(tile)
    expect(descendantsOfTile.filter(({ previewRendered }) => previewRendered)).toHaveLength(1)
    expect(descendantsOfTile.filter(({ type }) => type === 'button')).toHaveLength(1)
    expect(descendantsOfTile.map(({ textContent }) => textContent).filter(Boolean)).toEqual(['Accept'])
  })

  it('binds every active order tile to its own abandon callback', () => {
    // Catches loop capture or single-active-order assumptions.
    const h = harness()
    const gameProgress = progress({
      'blank-sprout': { kind: 'accepted', pot: { x: 0, z: 0, yaw: 0 } },
      'single-double-cut': { kind: 'accepted', pot: { x: 1, z: 1, yaw: 1 } },
    })
    h.controller.show(state({ progress: gameProgress, tools: new ToolInventory(gameProgress.acquiredToolIds) }))
    click(primaryTab(h.root, 'orders'))
    click(contextTab(h.root, 'active'))

    for (const action of byData(h.content, 'orderAction', 'abandon')) click(action)
    expect(h.calls.abandoned).toEqual(['blank-sprout', 'single-double-cut'])
  })

  it('accepts with the captured view and edits tiles instead in developer mode', () => {
    // Catches developer editing accidentally mutating order state or acceptance losing the camera view.
    const normal = harness()
    normal.controller.show(state())
    click(primaryTab(normal.root, 'orders'))
    click(byData(normal.content, 'orderAction', 'accept')[0]!)
    expect(normal.calls.accepted).toEqual([{ orderId: 'blank-sprout', view }])

    const developer = harness()
    developer.controller.show(state({ developerMode: true }))
    click(primaryTab(developer.root, 'orders'))
    click(byData(developer.content, 'orderId')[0]!)
    expect(developer.calls.edited).toEqual(['blank-sprout'])
    expect(developer.calls.accepted).toEqual([])
  })

  it('selects Orders and opens a fresh editor on every developer-mode Orders click', () => {
    // Catches creation only working on the transition from Tools to Orders.
    const h = harness()
    h.controller.show(state({ developerMode: true }))
    const orders = primaryTab(h.root, 'orders')

    click(orders)
    click(orders)

    expect(h.controller.selectedPrimaryTab).toBe('orders')
    expect(orders.ariaPressed).toBe('true')
    expect(h.calls.created).toBe(2)
  })

  it('preserves each primary tab contextual choice while the ledger stays open', () => {
    // Catches one shared contextual-tab state overwriting the other primary view.
    const h = harness()
    h.controller.show(state())
    click(contextTab(h.root, 'acquired'))
    click(primaryTab(h.root, 'orders'))
    click(contextTab(h.root, 'completed'))
    click(primaryTab(h.root, 'tools'))
    expect(contextTab(h.root, 'acquired').ariaPressed).toBe('true')
    click(primaryTab(h.root, 'orders'))
    expect(contextTab(h.root, 'completed').ariaPressed).toBe('true')
  })

  it('opens, focuses the selected primary tab, hides, and disposes listeners', () => {
    // Catches modal state/focus becoming opaque to the composing state controller.
    const h = harness()
    h.controller.show(state())
    const tools = primaryTab(h.root, 'tools')
    expect(h.root.hidden).toBe(false)
    expect(h.controller.isOpen).toBe(true)
    expect(tools.focusCalls).toBe(1)
    h.controller.hide()
    expect(h.controller.isOpen).toBe(false)
    h.controller.dispose()
    click(primaryTab(h.root, 'orders'))
    expect(h.controller.selectedPrimaryTab).toBe('tools')
  })
})
