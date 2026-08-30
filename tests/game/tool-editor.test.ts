import { describe, expect, it } from 'vitest'
import { attachWorldInput } from '../../game/input'
import { mountLedger, type LedgerState } from '../../game/ledger'
import {
  applyDeveloperToolsSetting,
  developerToolsSettingPorts,
  mountSettings,
} from '../../game/settings'
import { mountToolEditor } from '../../game/tool-editor'
import { WorldStateController } from '../../game/world-state'
import { initialCameraState } from '../../src/game/camera'
import type { GameProgress } from '../../src/game/model'
import { openingOrderCatalog } from '../../src/game/orders/catalog'
import { ToolInventory } from '../../src/game/tools'
import {
  decodeToolContent,
  LiveToolContent,
  openingToolContent,
  type ToolContentRevision,
} from '../../src/game/tools/content'

class TestElement extends EventTarget {
  hidden = false
  value = ''
  textContent = ''
  className = ''
  type = ''
  ariaPressed = 'false'
  tabIndex = -1
  checked = false
  width = 240
  height = 150
  readOnly = false
  isContentEditable = false
  parent: EventTarget | null = null
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []
  readonly style = { setProperty: (_name: string, _value: string): void => {} }

  constructor(readonly ownerDocument: TestDocument, readonly tagName: string) { super() }

  private disabledValue = false
  get disabled(): boolean { return this.disabledValue }
  set disabled(value: boolean) {
    this.disabledValue = value
    if (value && this.ownerDocument.activeElement === this) this.ownerDocument.activeElement = this.ownerDocument.body
  }

  append(...children: TestElement[]): void {
    for (const child of children) child.parent = this
    this.children.push(...children)
  }

  replaceChildren(...children: TestElement[]): void {
    for (const child of this.children) child.parent = null
    this.children.splice(0, this.children.length)
    this.append(...children)
  }

  contains(target: EventTarget | null): boolean {
    return target === this || this.children.some((child) => child.contains(target))
  }

  focus(): void { this.ownerDocument.activeElement = this }

  querySelector<ElementType extends Element>(selector: string): ElementType | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as ElementType
    for (const child of this.children) {
      const found = child.querySelector<ElementType>(selector)
      if (found !== null) return found
    }
    return null
  }

  override dispatchEvent(event: Event): boolean {
    if (!Object.hasOwn(event, 'composedPath')) Object.defineProperty(event, 'composedPath', { value: () => [this] })
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

class TestDocument extends EventTarget {
  activeElement: TestElement | null = null
  readonly body = new TestElement(this, 'BODY')
  parent: EventTarget | null = null

  constructor() { super(); this.body.parent = this }
  createElement(tagName: string): TestElement { return new TestElement(this, tagName.toUpperCase()) }
  override dispatchEvent(event: Event): boolean {
    const dispatched = super.dispatchEvent(event)
    if (event.bubbles && !event.cancelBubble) this.parent?.dispatchEvent(event)
    return dispatched && !event.defaultPrevented
  }
}

function element(documentTarget: TestDocument, dataName: string, tagName = 'div'): TestElement {
  const target = documentTarget.createElement(tagName)
  target.dataset[dataName] = ''
  return target
}

function revision(
  name = 'Synthetic iteration name',
  description = 'Synthetic iteration description.',
): ToolContentRevision {
  return decodeToolContent(openingToolContent.current.definitions.map((definition) => ({
    ...definition,
    name: definition.id === 'iteration' ? name : `Synthetic ${definition.id}`,
    description: definition.id === 'iteration'
      ? description
      : `Synthetic description for ${definition.id}.`,
  })))
}

function descendants(root: TestElement): readonly TestElement[] {
  return root.children.flatMap((child) => [child, ...descendants(child)])
}

function byData(root: TestElement, key: string, value?: string): readonly TestElement[] {
  return descendants(root).filter((candidate) => (
    Object.hasOwn(candidate.dataset, key)
    && (value === undefined || candidate.dataset[key] === value)
  ))
}

type Deferred = { promise: Promise<void>; resolve(): void; reject(error: Error): void }
function deferred(): Deferred {
  let resolve!: () => void
  let reject!: (error: Error) => void
  const promise = new Promise<void>((yes, no) => { resolve = yes; reject = no })
  return { promise, resolve, reject }
}

function harness(initial = revision()) {
  const windowTarget = new EventTarget()
  const documentTarget = new TestDocument()
  documentTarget.parent = windowTarget
  const root = element(documentTarget, 'toolEditor', 'section')
  root.hidden = true
  const form = element(documentTarget, 'toolEditorForm', 'form')
  const id = element(documentTarget, 'toolEditorId', 'input')
  const name = element(documentTarget, 'toolEditorName', 'input')
  const description = element(documentTarget, 'toolEditorDescription', 'textarea')
  const error = element(documentTarget, 'toolEditorError', 'p')
  const cancel = element(documentTarget, 'toolEditorCancel', 'button')
  const save = element(documentTarget, 'toolEditorSave', 'button')
  form.append(id, name, description, error, cancel, save)
  root.append(form)
  documentTarget.body.append(root)
  const live = new LiveToolContent(initial)
  const saved: ToolContentRevision[] = []
  let saveResult = Promise.resolve()
  let foreground = true
  const controller = mountToolEditor(root as unknown as HTMLElement, {
    currentRevision: () => live.current,
    isForeground: () => foreground,
    save: async (candidate) => { saved.push(candidate); await saveResult; live.publish(candidate) },
  })
  return {
    windowTarget, documentTarget, root, form, id, name, description, error, cancel, save,
    live, saved, controller,
    setSaveResult: (result: Promise<void>) => { saveResult = result },
    setForeground: (value: boolean) => { foreground = value },
  }
}

function submit(form: TestElement): void { form.dispatchEvent(new Event('submit', { bubbles: true, cancelable: true })) }
function key(code: string): Event {
  return Object.defineProperty(new Event('keydown', { bubbles: true, cancelable: true }), 'code', { value: code })
}
async function settle(): Promise<void> { await Promise.resolve(); await Promise.resolve() }

describe('tool editor controller', () => {
  it('shows immutable tool identity and publishes one complete edited revision', async () => {
    // Catches editable identity or a detached partial update replacing the whole content authority.
    const initial = revision()
    const h = harness(initial)
    h.controller.edit(h.live.current.definition('iteration'))
    expect(h.id.value).toBe('iteration')
    expect(h.id.readOnly).toBe(true)
    expect(h.name.value).toBe(initial.definition('iteration').name)
    expect(h.description.value).toBe(initial.definition('iteration').description)

    h.name.value = 'Edited synthetic name'
    h.description.value = 'Copies a selected cutting.'
    submit(h.form)
    await settle()

    expect(h.saved).toHaveLength(1)
    expect(h.saved[0]?.definitions).toHaveLength(openingToolContent.current.definitions.length)
    expect(h.saved[0]?.definition('iteration')).toEqual({
      id: 'iteration', name: 'Edited synthetic name', description: 'Copies a selected cutting.',
    })
    expect(h.controller.isOpen).toBe(false)
  })

  it('rejects blank name and description while preserving each draft', async () => {
    // Catches invalid authored copy reaching persistence or closing the recovery surface.
    for (const field of ['name', 'description'] as const) {
      const h = harness()
      h.controller.edit(h.live.current.definition('iteration'))
      h[field].value = '   '
      submit(h.form)
      await settle()
      expect(h.saved).toEqual([])
      expect(h.controller.isOpen).toBe(true)
      expect(h[field].value).toBe('   ')
      expect(h.error.textContent).toMatch(/non-blank/i)
    }
  })

  it('keeps the draft and prior live revision after permanent save rejects', async () => {
    // Catches publication-before-persistence or failed writes discarding recoverable edits.
    const initial = revision()
    const gate = deferred()
    const h = harness(initial)
    h.setSaveResult(gate.promise)
    h.controller.edit(initial.definition('iteration'))
    h.name.value = 'Unsaved name'
    h.description.value = 'Unsaved description'
    submit(h.form)
    gate.reject(new Error('repository is read-only'))
    await settle()

    expect(h.controller.isOpen).toBe(true)
    expect(h.name.value).toBe('Unsaved name')
    expect(h.description.value).toBe('Unsaved description')
    expect(h.error.textContent).toContain('repository is read-only')
    expect(h.save.disabled).toBe(false)
    expect(h.live.current).toBe(initial)
  })

  it('gives Backspace to editable text and closes only from noneditable foreground context', () => {
    // Catches text deletion closing the editor or a background draft intercepting Pause input.
    const h = harness()
    h.controller.edit(h.live.current.definition('iteration'))
    h.description.value = 'draft'
    const textBackspace = key('Backspace')
    h.description.dispatchEvent(textBackspace)
    expect(h.controller.isOpen).toBe(true)
    expect(textBackspace.defaultPrevented).toBe(false)

    h.save.focus()
    const close = key('Backspace')
    h.save.dispatchEvent(close)
    expect(h.controller.isOpen).toBe(false)
    expect(close.defaultPrevented).toBe(true)

    h.controller.edit(h.live.current.definition('iteration'))
    h.name.value = 'draft behind Pause'
    h.setForeground(false)
    const background = key('Backspace')
    h.save.dispatchEvent(background)
    expect(h.controller.isOpen).toBe(true)
    expect(h.name.value).toBe('draft behind Pause')
    expect(background.defaultPrevented).toBe(false)
  })

  it('leaves Escape to Pause and preserves the draft through Resume', () => {
    // Catches the editor consuming Escape or resetting the mounted form behind Pause.
    const h = harness()
    let paused = false
    const input = attachWorldInput(h.root as unknown as HTMLElement, {
      pointerDown: () => {}, pointerUp: () => {}, pointerCancel: () => {}, category: () => {},
      toggleLedger: () => {}, stepBack: () => {}, toggleDeveloperMode: () => {},
      pause: () => { paused = true }, engagementChanged: () => {},
    }, { window: h.windowTarget as Window, document: h.documentTarget as unknown as Document })
    input.suspend()
    h.controller.edit(h.live.current.definition('iteration'))
    h.name.value = 'draft behind Pause'
    const escape = key('Escape')
    h.name.dispatchEvent(escape)
    expect(paused).toBe(true)
    expect(h.controller.isOpen).toBe(true)
    input.resume()
    expect(h.name.value).toBe('draft behind Pause')
  })

  it('shuts down a foreground tool editor without releasing Pause or the open ledger', () => {
    // Catches Settings clearing only tutorial/order editors or reviving background world input.
    const h = harness()
    const ledgerRoot = element(h.documentTarget, 'ledger', 'section')
    ledgerRoot.hidden = true
    const primary = element(h.documentTarget, 'ledgerPrimaryTabs', 'nav')
    const context = element(h.documentTarget, 'ledgerContextTabs', 'nav')
    const content = element(h.documentTarget, 'ledgerContent')
    ledgerRoot.append(primary, context, content)
    const ledger = mountLedger(ledgerRoot as unknown as HTMLElement, {
      acquireTool: () => {}, acceptOrder: () => {}, abandonOrder: () => {},
      editOrder: () => {}, editTool: () => {}, createOrder: () => {},
    })
    const progress: GameProgress = {
      reputation: 0,
      orders: new Map(openingOrderCatalog.current.definitions.map(({ id }) => [
        id,
        { kind: 'pending' as const },
      ])),
      tutorialsEnabled: false,
      completedTutorialMilestones: new Set(),
      acquiredToolIds: new Set(['sprout-spawner']),
    }
    const tools = new ToolInventory(progress.acquiredToolIds)
    let developerMode = true
    let foreground: 'closed' | 'tool' = 'tool'
    const ledgerState = (): LedgerState => ({
      catalog: openingOrderCatalog.current,
      toolContent: h.live.current,
      progress,
      tools,
      tutorialCheck: () => true,
      developerMode,
      view: { eye: { x: 0, y: 1.7, z: 5 }, forward: { x: 0, y: 0, z: -1 } },
    })
    ledger.show(ledgerState())
    h.controller.edit(h.live.current.definition('double-cut'))
    expect(byData(content, 'toolEditable')).toHaveLength(2)

    let pauseVisible = false
    const inputCalls: string[] = []
    const camera = initialCameraState({ position: { x: 0, y: 1.7, z: 8 }, yaw: 0, pitch: 0 })
    const world = new WorldStateController({
      getCamera: () => camera,
      setCamera: () => {},
      tools,
      ledger,
      foreground: { get isOpen() { return foreground !== 'closed' } },
      input: {
        suspend: () => { inputCalls.push('suspend') },
        resume: () => { inputCalls.push('resume') },
        engage: () => { inputCalls.push('engage'); return Promise.resolve() },
      },
      pauseMenu: {
        show: () => { pauseVisible = true },
        hide: () => { pauseVisible = false },
      },
      worldName: () => 'Tool Orchard',
      setFreeActive: () => {}, cuttingCleared: () => {}, stateChanged: () => {},
    })
    world.pause()

    const settingsRoot = element(h.documentTarget, 'settings', 'section')
    settingsRoot.hidden = true
    const tutorials = element(h.documentTarget, 'settingsTutorials', 'input')
    const developerTools = element(h.documentTarget, 'settingsDeveloperTools', 'input')
    const back = element(h.documentTarget, 'settingsBack', 'button')
    settingsRoot.append(tutorials, developerTools, back)
    const settings = mountSettings(settingsRoot as unknown as HTMLElement, {
      setTutorialsEnabled: () => {},
      setDeveloperToolsEnabled: (enabled) => applyDeveloperToolsSetting(
        enabled,
        developerToolsSettingPorts({
          persist: () => {},
          setDeveloperMode: (value) => { developerMode = value },
          orderEditor: () => null,
          tutorialEditor: () => null,
          toolEditor: () => h.controller,
          clearForegroundEditor: () => { foreground = 'closed' },
          renderTutorial: () => {},
          refreshVisibleLedger: () => { ledger.show(ledgerState()) },
          mirrorRuntimeState: () => {},
        }),
      ),
      back: () => {},
    })
    settings.show({ tutorialsEnabled: false, developerToolsEnabled: true })
    developerTools.checked = false
    developerTools.dispatchEvent(new Event('change'))

    expect(h.controller.isOpen).toBe(false)
    expect(foreground).toBe('closed')
    expect(developerMode).toBe(false)
    expect(world.isPaused).toBe(true)
    expect(ledger.isOpen).toBe(true)
    expect(pauseVisible).toBe(true)
    expect(byData(content, 'toolEditable')).toHaveLength(0)
    expect(byData(content, 'toolAction', 'acquire')).toHaveLength(2)
    expect(inputCalls).toEqual(['suspend'])
  })
})
